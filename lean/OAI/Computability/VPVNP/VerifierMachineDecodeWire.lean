import OAI.Computability.VPVNP.UniversalMachine
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Ring

/-!
# The output wires of the coefficient machine's table decoder

A wire can test validity, recognize the empty program, or request a specific instruction at a
specific row and branch. A request records both tape updates and the target state.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace VerifierMachineDecode

open UniversalMachine

/-- The target state and the two symbol-and-motion pairs tested by an instruction query at
input length `n`. -/
abbrev InstructionKey (n : ℕ) := Fin (n + 2) × Fin 3 × Fin 3 × Fin 3 × Fin 3

/-- A decoder output testing validity, the empty program, or the instruction in a specific
transition slot. -/
inductive DecoderWire (n : ℕ)
  | valid
  | empty
  | slot (row : Fin (9 * n)) (branch : Bool) (key : InstructionKey n)
  deriving DecidableEq, Fintype

theorem decoderWire_card (n : ℕ) :
    Fintype.card (DecoderWire n) = 2 + 9 * n * 2 * (n + 2) * 81 := by
  let e : DecoderWire n ≃ Unit ⊕ Unit ⊕ (Fin (9 * n) × Bool × InstructionKey n) :=
    { toFun := fun | .valid => .inl () | .empty => .inr (.inl ())
                   | .slot i c k => .inr (.inr (i, c, k))
      invFun := fun | .inl _ => .valid | .inr (.inl _) => .empty
                    | .inr (.inr (i, c, k)) => .slot i c k
      left_inv := by intro q; cases q <;> rfl
      right_inv := by rintro (_ | (_ | ⟨i,c,k⟩)) <;> rfl }
  rw [Fintype.card_congr e]
  simp [InstructionKey]
  ring

/-- Read one branch slot of a row. A one-branch row uses the false slot. -/
def rowInstruction {extra : ℕ} : Branches extra → Bool → Option (Instruction extra)
  | .stop, _ => none
  | .one a, false => some a
  | .one _, true => none
  | .two a _, false => some a
  | .two _ b, true => some b

/-- The queried target, writes, and movements all agree with the literal instruction, comparing
target indices by value. -/
def KeyMatches {n extra : ℕ} (k : InstructionKey n) (a : Instruction extra) : Prop :=
  a.target.val = k.1.val ∧ a.firstSymbol = k.2.1 ∧ a.firstMove = k.2.2.1 ∧
    a.secondSymbol = k.2.2.2.1 ∧ a.secondMove = k.2.2.2.2

instance {n extra : ℕ} (k : InstructionKey n) (a : Instruction extra) :
    Decidable (KeyMatches k a) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The predicate on a decoded program expressed by a particular decoder output wire. -/
def wireHolds {n : ℕ} (p : Program) : DecoderWire n → Prop
  | .valid => True
  | .empty => p.extra = 0
  | .slot i c k =>
    ∃ row a, p.rows[i.val]? = some row ∧ rowInstruction row c = some a ∧ KeyMatches k a

/-- The global check on the running state count for the requested output. -/
def queryAllowed {n : ℕ} : DecoderWire n → ℕ → Prop
  | .valid, _ => True
  | .empty, extra => extra = 0
  | .slot i _ _, extra => i.val < 9 * extra

instance {n : ℕ} (q : DecoderWire n) (extra : ℕ) : Decidable (queryAllowed q extra) := by
  cases q <;> unfold queryAllowed <;> infer_instance

/-- Local constraint at the indexed row. -/
def keepRow {n extra : ℕ} : DecoderWire n → ℕ → Branches extra → Bool
  | .valid, _, _ | .empty, _, _ => true
  | .slot i c k, j, b => if j = i.val then
      (rowInstruction b c).any fun a => decide (KeyMatches k a)
    else true

/-- Every indexed row passes the requested decoder test, including the queried branch when its
row is reached. -/
def RowsKeep {n extra : ℕ} (q : DecoderWire n) (rows : List (Branches extra)) : Prop :=
  ∀ (i : ℕ) (b : Branches extra), rows[i]? = some b → keepRow q i b = true

theorem query_iff {n : ℕ} (q : DecoderWire n) (p : Program) :
    wireHolds p q ↔ queryAllowed q p.extra ∧ RowsKeep q p.rows := by
  cases q with
  | valid | empty => simp [wireHolds, queryAllowed, RowsKeep, keepRow]
  | slot i c k =>
    constructor
    · rintro ⟨b, a, hrow, ha, hk⟩
      have hi : i.val < p.rows.length := (List.getElem?_eq_some_iff.mp hrow).1
      refine ⟨by simpa [queryAllowed, p.rows_length, Nat.mul_comm] using hi, ?_⟩
      intro j b' hb'
      by_cases hj : j = i.val
      · subst j
        rw [hrow] at hb'
        cases hb'
        simp [keepRow, ha, hk]
      · simp [keepRow, hj]
    · rintro ⟨hi, h⟩
      have hlen : i.val < p.rows.length := by simpa [queryAllowed, p.rows_length, Nat.mul_comm] using hi
      let b := p.rows[i.val]
      have hb : p.rows[i.val]? = some b := List.getElem?_eq_getElem hlen
      have ha := h i.val b hb
      cases hx : rowInstruction b c with
      | none => simp [keepRow, hx] at ha
      | some a =>
        exact ⟨b, a, hb, hx, by simpa [keepRow, hx] using ha⟩

end VerifierMachineDecode

end VPVNP
end Computability
end OAI
