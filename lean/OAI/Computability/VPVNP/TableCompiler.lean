import OAI.Computability.VPVNP.UniversalMachine
import Mathlib.Data.Fintype.EquivFin

/-!
# Deterministic finite controls as literal transition tables

A control reads the head of the first tape and either halts or moves that head.
The compiled two-tape table preserves both tapes' symbols and the second head's
position. The ordering of the running states puts the given start state first.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TableCompiler

open UniversalMachine

/-- A deterministic read-only control action that halts with an acceptance bit or enters
another state with a specified motion of the first tape head. -/
inductive Step (Q : Type*) where
  | halt (accept : Bool)
  | move (next : Q) (dir : Fin 3)

variable {Q : Type*} [Fintype Q]

private theorem card_pos (start : Q) : 0 < Fintype.card Q :=
  Fintype.card_pos_iff.mpr ⟨start⟩

private noncomputable def numbering (start : Q) : Q ≃ Fin (Fintype.card Q) :=
  (Fintype.equivFin Q).trans (Equiv.swap (Fintype.equivFin Q start) ⟨0, card_pos start⟩)

private theorem numbering_start (start : Q) : (numbering start start).val = 0 := by
  simp [numbering]

private noncomputable def stateNumber (start q : Q) : Fin (Fintype.card Q + 2) :=
  ⟨(numbering start q).val + 2, Nat.add_lt_add_right (numbering start q).isLt 2⟩

private noncomputable def instruction (start : Q) (s : Step Q) (first second : Symbol) :
    Instruction (Fintype.card Q) :=
  match s with
  | .halt accept => ⟨⟨if accept then 1 else 0, by split <;> omega⟩, first, 0, second, 0⟩
  | .move next dir => ⟨stateNumber start next, first, dir, second, 0⟩

private def rowState (i : Fin (Fintype.card Q * 9)) : Fin (Fintype.card Q) :=
  ⟨i.val / 9, by omega⟩

private def rowFirst {m : ℕ} (i : Fin (m * 9)) : Symbol := ⟨i.val % 9 / 3, by omega⟩
private def rowSecond {m : ℕ} (i : Fin (m * 9)) : Symbol := ⟨i.val % 3, by omega⟩

private noncomputable def row (start : Q) (f : Q → Symbol → Step Q)
    (i : Fin (Fintype.card Q * 9)) : Branches (Fintype.card Q) :=
  .one (instruction start (f ((numbering start).symm (rowState i)) (rowFirst i))
    (rowFirst i) (rowSecond i))

/-- The nine rows per running state, in the order used by the literal machine. -/
noncomputable abbrev compile (start : Q) (f : Q → Symbol → Step Q) : Program :=
  ⟨Fintype.card Q, List.ofFn (row start f), List.length_ofFn⟩

/-- Running configuration corresponding to a finite control state. -/
noncomputable def running (start q : Q) (tape work : Turing.Tape Symbol) : Config (Fintype.card Q) :=
  ⟨stateNumber start q, tape, work⟩

/-- Motion of the read-only head, with the literal codes stay, left, right. -/
def moveTape (tape : Turing.Tape Symbol) (dir : Fin 3) : Turing.Tape Symbol :=
  match dir.val with
  | 0 => tape
  | 1 => tape.move .left
  | _ => tape.move .right

theorem initial_eq_running (start : Q) (f : Q → Symbol → Step Q) (input : Word) :
    initial (compile start f) input =
      running start start (Turing.Tape.mk₁ (input.map fun b => if b then 2 else 1))
        (Turing.Tape.mk₁ []) := by
  unfold initial running
  congr 1
  apply Fin.ext
  simp [compile, (card_pos start).ne', stateNumber, numbering_start]

private theorem lookup (start : Q) (f : Q → Symbol → Step Q) (q : Q)
    (tape work : Turing.Tape Symbol) :
    branches (compile start f) (running start q tape work) =
      .one (instruction start (f q tape.head) tape.head work.head) := by
  let j := (numbering start q).val * 9 + tape.head.val * 3 + work.head.val
  have hj : j < Fintype.card Q * 9 := by
    have := (numbering start q).isLt
    have := tape.head.isLt
    have := work.head.isLt
    dsimp [j]
    omega
  let i : Fin (Fintype.card Q * 9) := ⟨j, hj⟩
  have hs : rowState i = numbering start q := by
    apply Fin.ext
    change j / 9 = _
    have := tape.head.isLt
    have := work.head.isLt
    dsimp [j]
    omega
  have hfirst : rowFirst i = tape.head := by
    apply Fin.ext
    change j % 9 / 3 = _
    have := tape.head.isLt
    have := work.head.isLt
    dsimp [j]
    omega
  have hsecond : rowSecond i = work.head := by
    apply Fin.ext
    change j % 3 = _
    have := work.head.isLt
    dsimp [j]
    omega
  have hrow : row start f i = .one (instruction start (f q tape.head) tape.head work.head) := by
    simp [row, hs, hfirst, hsecond]
  unfold branches compile running stateNumber
  simp only [Nat.add_sub_cancel]
  change (List.ofFn (row start f))[j]?.getD .stop = _
  rw [List.getElem?_eq_getElem (by simpa using hj)]
  simpa only [Option.getD_some, List.getElem_ofFn] using hrow

theorem paths_running_succ (start : Q) (f : Q → Symbol → Step Q) (q : Q)
    (tape work : Turing.Tape Symbol) (fuel : ℕ) :
    paths (compile start f) (fuel + 1) (running start q tape work) =
      match f q tape.head with
      | .halt b => if b then 1 else 0
      | .move next dir => paths (compile start f) fuel (running start next (moveTape tape dir) work) := by
  have h1 : (running start q tape work).state.val ≠ 1 := by
    change (numbering start q).val + 2 ≠ 1
    omega
  have h0 : (running start q tape work).state.val ≠ 0 := by
    change (numbering start q).val + 2 ≠ 0
    omega
  rw [paths]
  simp only [ite_eq_right h1, ite_eq_right h0, lookup]
  cases f q tape.head with
  | halt b =>
    cases b
    · exact paths_reject _ _ rfl _
    · exact paths_accept _ _ rfl _
  | move next dir =>
    congr 1

end TableCompiler

end VPVNP
end Computability
end OAI
