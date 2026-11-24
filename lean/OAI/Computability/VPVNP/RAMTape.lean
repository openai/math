import OAI.Computability.VPVNP.UniversalMachine
import Mathlib.Data.Fintype.EquivFin

/-!
# Writable nondeterministic controls for the coefficient machine

A named finite control can inspect both head symbols, write and move both tapes,
and make a binary choice. The compiler emits the nine literal rows for each state.
Each occupied branch slot contributes its own path count.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape

open UniversalMachine

/-- Halting or two-head transition with a named successor state. -/
inductive Command (Q : Type*) where
  | halt (accept : Bool)
  | next (state : Q) (firstSymbol firstMove secondSymbol secondMove : Fin 3)

/-- The occupied nondeterministic branch slots of one table row. -/
inductive Choices (Q : Type*) where
  | stop
  | one (a : Command Q)
  | two (a b : Command Q)

/-- The commands available at each state and pair of scanned symbols. -/
abbrev Control (Q : Type*) := Q → Symbol → Symbol → Choices Q

variable {Q : Type*} [Fintype Q]

private theorem card_pos (start : Q) : 0 < Fintype.card Q :=
  Fintype.card_pos_iff.mpr ⟨start⟩

private noncomputable def number (start : Q) : Q ≃ Fin (Fintype.card Q) :=
  (Fintype.equivFin Q).trans (Equiv.swap (Fintype.equivFin Q start) ⟨0, card_pos start⟩)

private noncomputable def target (start q : Q) : Fin (Fintype.card Q + 2) :=
  ⟨(number start q).val + 2, by have := (number start q).isLt; omega⟩

/-- Encode one named command as a universal-machine instruction. -/
noncomputable def instruction (start : Q) : Command Q → Instruction (Fintype.card Q)
  | .halt b => ⟨⟨if b then 1 else 0, by split <;> omega⟩, 0, 0, 0, 0⟩
  | .next q a d b e => ⟨target start q, a, d, b, e⟩

/-- Encode the occupied branch slots, preserving their multiplicities. -/
noncomputable def records (start : Q) : Choices Q → Branches (Fintype.card Q)
  | .stop => .stop
  | .one a => .one (instruction start a)
  | .two a b => .two (instruction start a) (instruction start b)

private noncomputable def row (start : Q) (code : Control Q)
    (i : Fin (Fintype.card Q * 9)) : Branches (Fintype.card Q) :=
  records start (code ((number start).symm ⟨i.val / 9, by omega⟩)
    ⟨i.val % 9 / 3, by omega⟩ ⟨i.val % 3, by omega⟩)

/-- The physical table for a fixed finite control. -/
noncomputable abbrev compile (start : Q) (code : Control Q) : Program :=
  ⟨Fintype.card Q, List.ofFn (row start code), List.length_ofFn⟩

/-- Physical configuration of a named nonhalting state and its two tapes. -/
noncomputable def running (start q : Q) (t u : Turing.Tape Symbol) : Config (Fintype.card Q) :=
  ⟨target start q, t, u⟩

/-- The two halting states precede every encoded control state. -/
theorem running_state_ge_two (start q : Q) (t u : Turing.Tape Symbol) :
    2 ≤ (running start q t u).state.val := by
  change 2 ≤ (number start q).val + 2
  omega

theorem initial_eq_running (start : Q) (code : Control Q) (input : Word) :
    initial (compile start code) input =
      running start start (Turing.Tape.mk₁ (input.map fun b => if b then 2 else 1))
        (Turing.Tape.mk₁ []) := by
  unfold initial running
  congr 1
  apply Fin.ext
  simp [compile, (card_pos start).ne', target, number]

theorem lookup (start : Q) (code : Control Q) (q : Q) (t u : Turing.Tape Symbol) :
    branches (compile start code) (running start q t u) = records start (code q t.head u.head) := by
  let j := (number start q).val * 9 + t.head.val * 3 + u.head.val
  have hq := (number start q).isLt
  have ha := t.head.isLt
  have hb := u.head.isLt
  have hj : j < Fintype.card Q * 9 := by dsimp [j]; omega
  unfold branches compile running target
  simp only [Nat.add_sub_cancel]
  change (List.ofFn (row start code))[j]?.getD .stop = _
  rw [List.getElem?_eq_getElem (by simpa using hj)]
  simp only [Option.getD_some, List.getElem_ofFn, row]
  have h₁ : (⟨j / 9, by omega⟩ : Fin (Fintype.card Q)) = number start q :=
    Fin.ext (by dsimp [j]; omega)
  have h₂ : (⟨j % 9 / 3, by omega⟩ : Symbol) = t.head := Fin.ext (by dsimp [j]; omega)
  have h₃ : (⟨j % 3, by omega⟩ : Symbol) = u.head := Fin.ext (by dsimp [j]; omega)
  simp [h₁, h₂, h₃]

/-- Accepting paths from the given named configuration within the tape clock. -/
noncomputable abbrev count (start : Q) (code : Control Q) (ticks : ℕ) (q : Q)
    (t u : Turing.Tape Symbol) := paths (compile start code) ticks (running start q t u)

/-- The contribution of one executed command to the remaining accepting path count. -/
noncomputable def after (start : Q) (code : Control Q) (ticks : ℕ) (t u : Turing.Tape Symbol) :
    Command Q → ℕ
  | .halt b => b.toNat
  | .next q a d b e => count start code ticks q (updateTape t a d) (updateTape u b e)

private theorem paths_advance (start : Q) (code : Control Q) (ticks : ℕ) (q : Q)
    (t u : Turing.Tape Symbol) (a : Command Q) :
    paths (compile start code) ticks (advance (running start q t u) (instruction start a)) =
      after start code ticks t u a := by
  cases a with
  | halt b => cases b <;> first | exact paths_reject _ _ rfl _ | exact paths_accept _ _ rfl _
  | next => rfl

/-- A literal binary row adds two counts, including when its targets agree. -/
theorem paths_step (start : Q) (code : Control Q) (ticks : ℕ) (q : Q)
    (t u : Turing.Tape Symbol) :
    count start code (ticks + 1) q t u =
      match code q t.head u.head with
      | .stop => 0
      | .one a => after start code ticks t u a
      | .two a b => after start code ticks t u a + after start code ticks t u b := by
  have h₁ : (running start q t u).state.val ≠ 1 := by change (number start q).val + 2 ≠ 1; omega
  have h₀ : (running start q t u).state.val ≠ 0 := by change (number start q).val + 2 ≠ 0; omega
  rw [count, paths]
  simp only [ite_eq_right h₁, ite_eq_right h₀, lookup]
  cases code q t.head u.head <;> simp only [records, paths_advance]

end RAMTape

end VPVNP
end Computability
end OAI
