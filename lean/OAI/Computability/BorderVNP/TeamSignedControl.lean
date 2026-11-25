import OAI.Computability.BorderVNP.SignedPaths
import OAI.Computability.VPVNP.RAMTapeRun

/-! # Physical tape controls with signed halts

A finite control may mark any accepting instruction as negative. The literal table records
that sign in the second tape's head at the halt, using the same clock and continuing commands
as the original two-tape interpreter. Distinct branch slots retain their multiplicities.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTape

open VPVNP.RAMTape VPVNP.UniversalMachine Turing

variable {Q : Type*} [Fintype Q]

private noncomputable def number (start : Q) : Q ≃ Fin (Fintype.card Q) :=
  (Fintype.equivFin Q).trans (Equiv.swap (Fintype.equivFin Q start)
    ⟨0, Fintype.card_pos_iff.mpr ⟨start⟩⟩)

/-- Encode a signed halt by writing the sign symbol without moving the work head. -/
noncomputable def signedInstruction (start : Q) (negative : Bool) :
    Command Q → Instruction (Fintype.card Q)
  | .halt b => { instruction start (.halt b) with secondSymbol := if negative then 2 else 0 }
  | cmd => instruction start cmd

private noncomputable def encodeRow (start : Q) (neg : Bool) : Choices Q → Branches (Fintype.card Q)
  | .stop => .stop
  | .one a => .one (signedInstruction start neg a)
  | .two a b => .two (signedInstruction start neg a) (signedInstruction start neg b)

/-- Compile the full signed finite control into a literal two-tape program. -/
noncomputable abbrev table (start : Q) (code : Control Q) (neg : Q → Bool) : Program :=
  ⟨Fintype.card Q, List.ofFn fun i : Fin (Fintype.card Q * 9) =>
    let q := (number start).symm ⟨i.val / 9, by omega⟩
    encodeRow start (neg q) (code q ⟨i.val % 9 / 3, by omega⟩ ⟨i.val % 3, by omega⟩),
    List.length_ofFn⟩

private theorem lookup_signed (start : Q) (code : Control Q) (neg : Q → Bool) (q : Q)
    (t u : Tape Symbol) : branches (table start code neg) (running start q t u) =
      encodeRow start (neg q) (code q t.head u.head) := by
  let j := (number start q).val * 9 + t.head.val * 3 + u.head.val
  have hq := (number start q).isLt
  have hx := t.head.isLt
  have hy := u.head.isLt
  have hj : j < Fintype.card Q * 9 := by dsimp [j]; omega
  have hs : (running start q t u).state.val = (number start q).val + 2 := rfl
  unfold branches
  rw [hs, Nat.add_sub_cancel]
  change ((table start code neg).rows[j]?).getD (Branches.stop) = _
  unfold table
  rw [List.getElem?_eq_getElem (by simpa using hj)]
  simp only [Option.getD_some, List.getElem_ofFn]
  have h₁ : (⟨j / 9, by omega⟩ : Fin (Fintype.card Q)) = number start q :=
    Fin.ext (by dsimp [j]; omega)
  have h₂ : (⟨j % 9 / 3, by omega⟩ : Symbol) = t.head := Fin.ext (by dsimp [j]; omega)
  have h₃ : (⟨j % 3, by omega⟩ : Symbol) = u.head := Fin.ext (by dsimp [j]; omega)
  simp [h₁, h₂, h₃]

/-- Signed path count starting in a named state of the literal program. -/
noncomputable def value (start : Q) (code : Control Q) (neg : Q → Bool) (ticks : ℕ)
    (q : Q) (t u : Tape Symbol) : ℤ :=
  signedPaths (table start code neg) ticks (running start q t u)

/-- Contribution of a terminal instruction with its sign. -/
def haltWeight (accept negative : Bool) : ℤ := if accept then if negative then -1 else 1 else 0

/-- Value after carrying out one signed control command. -/
noncomputable def after (start : Q) (code : Control Q) (neg : Q → Bool) (ticks : ℕ)
    (q : Q) (t u : Tape Symbol) : Command Q → ℤ
  | .halt b => haltWeight b (neg q)
  | .next r x d y e => value start code neg ticks r (updateTape t x d) (updateTape u y e)

private theorem signed_advance (start : Q) (code : Control Q) (neg : Q → Bool) (ticks : ℕ)
    (q : Q) (t u : Tape Symbol) (cmd : Command Q) :
    signedPaths (table start code neg) ticks
      (advance (running start q t u) (signedInstruction start (neg q) cmd)) =
      after start code neg ticks q t u cmd := by
  cases cmd with
  | next => rfl
  | halt b =>
    cases b <;> cases hn : neg q <;> cases ticks <;>
      simp [signedPaths, signedInstruction, haltOutput, after, haltWeight, advance, instruction,
        updateTape, Tape.write, hn]

/-- A row in the signed physical table has exactly its prescribed signed sum of continuations. -/
theorem value_step (start : Q) (code : Control Q) (neg : Q → Bool) (ticks : ℕ) (q : Q)
    (t u : Tape Symbol) : value start code neg (ticks + 1) q t u =
      match code q t.head u.head with
      | .stop => 0
      | .one a => after start code neg ticks q t u a
      | .two a b => after start code neg ticks q t u a + after start code neg ticks q t u b := by
  have hs := running_state_ge_two start q t u
  have h1 : (running start q t u).state.val ≠ 1 := by omega
  have h0 : (running start q t u).state.val ≠ 0 := by omega
  unfold value
  rw [signedPaths.eq_def]
  simp only [h1, h0, ↓reduceIte, lookup_signed]
  cases code q t.head u.head <;> simp only [encodeRow, signed_advance]

/-- Deterministic tape runs preserve every subsequent signed contribution. -/
theorem runs_value {code : Control Q} {n q t u q' x y} (h : Runs code n q t u q' x y)
    (start : Q) (neg : Q → Bool) (fuel : ℕ) :
    value start code neg (fuel + n) q t u = value start code neg fuel q' x y := by
  induction h with
  | nil => rfl
  | cons hs _ ih => rw [Nat.add_succ, value_step, hs]; exact ih

end TeamTape

end BorderVNP
end Computability
end OAI
