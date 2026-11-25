import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotTracks

/-! # Erasing a scheduler tally and rewinding to its marked origin -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.SlotErase
open IntegerMultiplication TM

variable {D : Type}

abbrev State := RoundExpose.State

def rule (clear : D → D) (origin : D → Bool) : Rule (Option Bool × D) State Unit := fun q h =>
  let c := h ()
  match q with
  | .scan => if c.1.isSome then some (.scan, fun _ => ((none,clear c.2),.right))
    else some (.rewind,fun _ => (c,.stay))
  | .rewind => if origin c.2 then some (.done,fun _ => (c,.stay))
    else some (.rewind,fun _ => (c,.left))
  | .done => none

private def interval (l n : ℕ) (p : ℤ) : Tape (Option Bool) :=
  ⟨p,fun d => if l ≤ p+d ∧ p+d < n then some true else none⟩

private def cfg (code : ℤ → Option Bool → D) (q : State) (l n : ℕ) (p : ℤ) :
    Config (Option Bool × D) State Unit :=
  ⟨q,fun _ => SlotTracks.tape code (interval l n p)⟩

variable (clear : D → D) (origin : D → Bool) (code : ℤ → Option Bool → D)
    (hc : ∀ p b, clear (code p b) = code p none)
    (ho : ∀ p, origin (code p none) = decide (p=0))

include hc in
private theorem erase_step {k n : ℕ} (h : k<n) :
    advance (rule clear origin) (cfg code .scan k n k) = some (cfg code .scan (k+1) n (k+1 : ℕ)) := by
  simp only [advance,rule,cfg,SlotTracks.tape,interval,Int.add_zero,le_refl,Nat.cast_lt,
    h,and_self,ite_true,Option.isSome_some,Option.map_some,Option.some.injEq,Config.mk.injEq,true_and]
  funext j
  simp only [Tape.apply,Move.shift,Nat.cast_add,Nat.cast_one,Tape.mk.injEq,true_and,hc]
  funext d
  split_ifs <;> grind

private theorem turn (n : ℕ) :
    advance (rule clear origin) (cfg code .scan n n n) = some (cfg code .rewind n n n) := by
  unfold advance
  change Option.map _ (rule clear origin .scan _) = _
  simp only [rule,cfg,SlotTracks.tape,interval,Int.add_zero,lt_self_iff_false,and_false,ite_false,
    Option.isSome_none,Bool.false_eq_true,Option.map_some,Option.some.injEq,Config.mk.injEq,true_and]
  funext j
  simpa [cfg,SlotTracks.tape,interval] using SM.Action.apply_stay ((cfg code .scan n n n).tape ())

include ho in
private theorem back_step (k n : ℕ) :
    advance (rule clear origin) (cfg code .rewind n n (k+1 : ℕ)) = some (cfg code .rewind n n k) := by
  have absent (p : ℤ) : ¬ ((n : ℤ) ≤ p ∧ p < n) := by omega
  simp only [advance,rule,cfg,SlotTracks.tape,interval,absent,ite_false,Int.add_zero,ho,Nat.cast_add,
    Nat.cast_one,show (k : ℤ)+1 ≠ 0 by omega,
    decide_false,Bool.false_eq_true,Option.map_some,Option.some.injEq,Config.mk.injEq,true_and]
  funext j
  simp only [Tape.apply,Move.shift,Tape.mk.injEq]
  constructor
  · omega
  · funext d
    split_ifs <;> grind

include ho in
private theorem done_step (n : ℕ) :
    advance (rule clear origin) (cfg code .rewind n n 0) = some (cfg code .done n n 0) := by
  have absent (p : ℤ) : ¬ ((n : ℤ) ≤ p ∧ p < n) := by omega
  simp only [advance,rule,cfg,SlotTracks.tape,interval,absent,ite_false,Int.add_zero,ho,
    decide_true,ite_true,Option.map_some,Option.some.injEq,Config.mk.injEq,true_and]
  funext j
  simpa [cfg,SlotTracks.tape,interval,absent] using SM.Action.apply_stay ((cfg code .rewind n n 0).tape ())

include ho in
private theorem backwards (k n : ℕ) :
    Trace (advance (rule clear origin)) (cfg code .rewind n n k) (k+1) (cfg code .done n n 0) := by
  induction k with
  | zero => exact .single (done_step clear origin code ho n)
  | succ k ih => simpa [Nat.add_comm] using Trace.cons (back_step clear origin code ho k n) ih

include hc ho in
private theorem forwards (k d n : ℕ) (h : k+d=n) :
    Trace (advance (rule clear origin)) (cfg code .scan k n k) (d+1+(n+1)) (cfg code .done n n 0) := by
  induction d generalizing k with
  | zero => subst n; exact .cons (turn clear origin code _) (backwards clear origin code ho _ _)
  | succ d ih =>
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
      (Trace.cons (erase_step clear origin code hc (show k<n by omega)) (ih (k+1) (by omega)))

include hc ho in
/-- The scan changes both the unary marks and the saved tally data, then returns
the head to its original position. The two changes of phase are charged. -/
theorem erase (n : ℕ) :
    Trace (advance (rule clear origin))
      ⟨.scan,fun _ => SlotTracks.tape code (RoundExpose.word n 0)⟩ (2*n+2)
      ⟨.done,fun _ => SlotTracks.tape code (RoundExpose.word 0 0)⟩ := by
  have H := forwards clear origin code hc ho 0 n n (by omega)
  have hz : interval n n 0 = RoundExpose.word 0 0 := by
    simp [interval,RoundExpose.word,Tape.mk.injEq]
    funext k; split_ifs <;> first | rfl | omega
  rw [show 2*n+2 = n+1+(n+1) by omega]
  have hi : interval 0 n 0 = RoundExpose.word n 0 := by simp [interval,RoundExpose.word]
  simpa only [cfg,Nat.cast_zero,hz,hi] using H

end Uniform.SlotErase

end NearSquareRoot
end Computability
end OAI
