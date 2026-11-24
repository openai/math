import OAI.Computability.VPVNP.RAMTapeSpacePaths
import OAI.Computability.VPVNP.VerifierMachineSimulation

/-!
# Head displacement of a literal compiled table on a choice string

A bit selecting an instruction contributes the two moves in that record.
Rejection of an invalid choice and all padding after a halt leave both head
positions fixed. The continuing records form a prefix of a path through the
source control with exactly the displacement of the whole literal run.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape

open UniversalMachine Turing

/-- Read the moves of the instruction actually selected by a witness bit. -/
def choiceMotion (p : Program) (c : Config p.extra) (bit : Bool) : ℤ × ℤ :=
  if 2 ≤ c.state.val then
    match chosenInstruction (branches p c) bit with
    | none => (0, 0)
    | some a => (moveDelta a.firstMove, moveDelta a.secondMove)
  else (0, 0)

/-- Sum the moves from the literal rows, evolving the same configuration as
`acceptsChoices` on each bit. -/
def choiceDisplacement (p : Program) : Config p.extra → List Bool → ℤ × ℤ
  | _, [] => (0, 0)
  | c, b :: bs => choiceMotion p c b + choiceDisplacement p (choiceStep p c b) bs

private theorem halted_step (p : Program) (c : Config p.extra) (b : Bool) (h : c.state.val < 2) :
    (choiceStep p c b).state.val < 2 := by
  by_cases ha : c.state.val = 1
  · cases b <;> simp [choiceStep, ha, reject]
  · have hr : c.state.val = 0 := by omega
    simp [choiceStep, hr]

private theorem halted_displacement (p : Program) (c : Config p.extra) (bits : List Bool)
    (h : c.state.val < 2) : choiceDisplacement p c bits = (0, 0) := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
    rw [choiceDisplacement, ih _ (halted_step p c b h)]
    simp [choiceMotion, Nat.not_le_of_lt h]

variable {Q : Type*}

private def selected (row : Choices Q) (bit : Bool) : Option (Command Q) :=
  match row with
  | .stop => none
  | .one a => if bit then none else some a
  | .two a b => some (if bit then b else a)

private theorem contains_selected {row : Choices Q} {b : Bool} {a : Command Q} (h : selected row b = some a) :
    row.contains a := by
  cases row <;> cases b <;> simp_all [Choices.contains, selected]

variable [Fintype Q]

private theorem literal_selection (start : Q) (code : Control Q) (q : Q) (t u : Tape Symbol) (b : Bool) :
    let c := running start q t u
    let p := compile start code
    let sel := selected (code q t.head u.head) b
    choiceStep p c b = sel.elim (reject c) (fun a => advance c (instruction start a)) ∧
    choiceMotion p c b = sel.elim (0, 0) (fun a =>
      (moveDelta (instruction start a).firstMove, moveDelta (instruction start a).secondMove)) := by
  dsimp only
  have hr := running_state_ge_two start q t u
  have ha : (running start q t u).state.val ≠ 1 := by omega
  have hz : (running start q t u).state.val ≠ 0 := by omega
  simp only [choiceStep, choiceMotion, hr, ha, hz, ite_true, ite_false, lookup]
  cases code q t.head u.head <;> cases b <;> exact ⟨rfl, rfl⟩

/-- Every prefix of padded witness bits has the net motion of a prefix of
continuing source commands, even when a later witness bit invalidates it. -/
theorem choiceDisplacement_path (start : Q) (code : Control Q) (q : Q) (t u : Tape Symbol)
    (bits : List Bool) :
    let d := choiceDisplacement (compile start code) (running start q t u) bits
    ∃ n ≤ bits.length, ∃ r x y, HeadPath code n d.1 d.2 q t u r x y := by
  induction bits generalizing q t u with
  | nil => exact ⟨0, by simp, q, t, u, .nil ..⟩
  | cons b bs ih =>
    dsimp only
    obtain ⟨hc, hm⟩ := literal_selection start code q t u b
    rw [choiceDisplacement, hc, hm]
    cases hs : selected (code q t.head u.head) b with
    | none =>
      simp only [Option.elim_none]
      rw [halted_displacement _ _ _ (by simp [reject])]
      exact ⟨0, by omega, q, t, u, .nil ..⟩
    | some cmd =>
      simp only [Option.elim_some]
      cases cmd with
      | halt accept =>
        have hh : (advance (running start q t u) (instruction start (.halt accept))).state.val < 2 := by
          cases accept <;> simp [advance, instruction]
        rw [halted_displacement _ _ _ hh]
        exact ⟨0, by omega, q, t, u, .nil ..⟩
      | next v a d a' e =>
        obtain ⟨n, hn, r, x, y, hp⟩ := ih v (updateTape t a d) (updateTape u a' e)
        exact ⟨n+1, by simp; omega, r, x, y, .cons (contains_selected hs) hp⟩

end RAMTape

end VPVNP
end Computability
end OAI
