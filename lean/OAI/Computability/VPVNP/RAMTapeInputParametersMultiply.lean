import OAI.Computability.VPVNP.TallyStacks
import Mathlib.Tactic.Ring

/-!
# Fixed unary multiplication for the live input parameters

Transfer the left factor to the outer scratch stack. For each of its tally marks,
restore one mark to the left input and add a copy of the right input to the accumulator.
The two inputs and both scratch stacks are restored at the normal return.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Tally

open Routine

variable {K : Type*}

/-- Add the product of the two input tallies to `dst`. -/
def mulAdd (lhs rhs dst outer tmp : K) :=
  let body := (Routine.push lhs true).followedBy (copyAdd rhs dst tmp)
  (move lhs outer).followedBy (Routine.popLoop outer (fun _ => true) body body)

variable [DecidableEq K]

/-- Frame for the three stacks that change during the outer loop. -/
private def mulFrame (s : State K) (lhs dst outer : K) (a d n : ℕ) : State K :=
  fun i => if i = lhs then a else if i = dst then d else if i = outer then n else s i

theorem mulAdd_runs (lhs rhs dst outer tmp : K) (hd : [lhs, rhs, dst, outer, tmp].Nodup)
    (s : State K) (ho : s outer = 0) (ht : s tmp = 0) :
    (mulAdd lhs rhs dst outer tmp).Runs (s lhs * (5 * s rhs + 6) + 2)
      (encode s) (encode (Function.update s dst (s dst + s lhs * s rhs))) := by
  simp [List.nodup_cons] at hd
  obtain ⟨⟨hlr, hld, hlo, hlt⟩, ⟨hrd, hro, hrt⟩, ⟨hdo, hdt⟩, hot⟩ := hd
  let frame := mulFrame s lhs dst outer
  have setL (a d n v : ℕ) : Function.update (frame a d n) lhs v = frame v d n := by
    funext i
    by_cases h : i = lhs <;> simp [frame, mulFrame, h]
  have setD (a d n v : ℕ) : Function.update (frame a d n) dst v = frame a v n := by
    funext i
    by_cases h : i = dst <;> simp [frame, mulFrame, h, Ne.symm hld]
  have setO (a d n v : ℕ) : Function.update (frame a d n) outer v = frame a d v := by
    funext i
    by_cases h : i = outer <;> simp [frame, mulFrame, h, Ne.symm hlo, Ne.symm hdo]
  let states (i : ℕ) := frame (s lhs - i) (s dst + (s lhs - i) * s rhs) i
  let body := (Routine.push lhs true).followedBy (copyAdd rhs dst tmp)
  have hstates (i : ℕ) (_ : i ≤ s lhs) : states i outer = i := by
    simp [states, frame, mulFrame, Ne.symm hlo, Ne.symm hdo]
  have hbody (i : ℕ) (hi : i < s lhs) :
      body.Runs (1 + (5 * s rhs + 2)) (encode (Function.update (states (i+1)) outer i))
        (encode (states i)) := by
    let a := s lhs - (i + 1)
    let d := s dst + a * s rhs
    have hpop : Function.update (states (i+1)) outer i = frame a d i := setO _ _ _ _
    have hsucc : a + 1 = s lhs - i := by dsimp [a]; omega
    have hpush := increment (frame a d i) lhs
    have hval : (frame a d i) lhs = a := by simp [frame, mulFrame]
    rw [hval, setL] at hpush
    have htmp : (frame (a+1) d i) tmp = 0 := by
      simp [frame, mulFrame, Ne.symm hlt, Ne.symm hdt, Ne.symm hot, ht]
    have hcopy := copyAdd_runs rhs dst tmp hrd hrt hdt (frame (a+1) d i) htmp
    have hright : (frame (a+1) d i) rhs = s rhs := by
      simp [frame, mulFrame, Ne.symm hlr, hrd, hro]
    have hdst : (frame (a+1) d i) dst = d := by simp [frame, mulFrame, Ne.symm hld]
    rw [hright, hdst, setD] at hcopy
    have hout : frame (a+1) (d + s rhs) i = states i := by
      unfold states
      rw [← hsucc, Nat.succ_mul]
      simp [d, Nat.add_assoc]
    rw [hpop, ← hout]
    exact hpush.followedBy hcopy
  have hloop := drainRuns outer body states (fun _ => 1 + (5 * s rhs + 2)) (s lhs) hstates hbody
  have hmove := move_runs lhs outer hlo s
  have hstart : Function.update (Function.update s lhs 0) outer (s outer + s lhs) = states (s lhs) := by
    funext i
    by_cases he : i = lhs <;> by_cases he' : i = outer <;>
      simp_all [states, frame, mulFrame, Ne.symm hdo, Ne.symm hlo]
  have hend : states 0 = Function.update s dst (s dst + s lhs * s rhs) := by
    funext i
    by_cases he : i = dst <;> by_cases he' : i = lhs <;> by_cases he'' : i = outer <;>
      simp_all [states, frame, mulFrame, Ne.symm hdo, Ne.symm hlo, Ne.symm hld]
  rw [hstart] at hmove
  rw [hend] at hloop
  have h := hmove.followedBy hloop
  convert! h using 1
  simp
  ring

end RAMTape.Tally

end VPVNP
end Computability
end OAI
