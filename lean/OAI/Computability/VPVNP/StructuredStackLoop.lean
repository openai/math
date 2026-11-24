import OAI.Computability.VPVNP.StructuredStackLink

/-!
# Exact instruction costs of a structured stack loop

An empty pop returns immediately. A nonempty pop spends one instruction before
entering its body, whose normal return either finishes the loop or resumes at
the next pop. The bodies may use any of the stacks, including the stack scanned.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Routine.Runs

variable {K Q R : Type*} [DecidableEq K]
variable (k : K) (repeatOn : Bool → Bool) (low : Routine K Q) (high : Routine K R)
variable {s mid out : Stacks K} {tail : List Bool} {n m : ℕ}

private def nextState (bit : Option Bool) : Option (Unit ⊕ (Q ⊕ R)) :=
  match bit with
  | none => none
  | some false => some (.inr (.inl low.entry))
  | some true => some (.inr (.inr high.entry))

private theorem enter :
    StackStep (popLoop k repeatOn low high).standalone
      (some (popLoop k repeatOn low high).entry) s (nextState low high (s k).head?)
      (Function.update s k (s k).tail) :=
  StackStep.pop rfl

/-- The terminating empty pop preserves the stacks. -/
theorem popLoop_empty (hstack : s k = []) :
    (popLoop k repeatOn low high).Runs 1 s s := by
  have hs := enter k repeatOn low high (s := s)
  rw [hstack] at hs
  have hup : Function.update s k ([] : List Bool) = s := by
    rw [← hstack]
    exact Function.update_eq_self k s
  change StackStep _ _ s none (Function.update s k []) at hs
  rw [hup] at hs
  exact .cons hs (.nil ..)

private theorem popLoop_body {b : Bool} (hstack : s k = b :: tail)
    (hbody : if b then high.Runs n (Function.update s k tail) mid
      else low.Runs n (Function.update s k tail) mid) :
    StackRuns (popLoop k repeatOn low high).standalone (n + 1)
      (some (popLoop k repeatOn low high).entry) s
      (if repeatOn b then some (popLoop k repeatOn low high).entry else none) mid := by
  have hs := enter k repeatOn low high (s := s)
  rw [hstack] at hs
  cases b with
  | false =>
    have hb : low.Runs n (Function.update s k tail) mid := hbody
    exact .cons hs (hb.link _ (Sum.inr ∘ Sum.inl) _ (fun _ => rfl))
  | true =>
    have hb : high.Runs n (Function.update s k tail) mid := hbody
    exact .cons hs (hb.link _ (Sum.inr ∘ Sum.inr) _ (fun _ => rfl))

/-- A continuing iteration costs one pop plus the body and the remaining loop. -/
theorem popLoop_continue {b : Bool} (hstack : s k = b :: tail) (hrep : repeatOn b = true)
    (hbody : if b then high.Runs n (Function.update s k tail) mid
      else low.Runs n (Function.update s k tail) mid)
    (hrest : (popLoop k repeatOn low high).Runs m mid out) :
    (popLoop k repeatOn low high).Runs (1 + n + m) s out := by
  have h := popLoop_body k repeatOn low high hstack hbody
  rw [ite_eq_left hrep] at h
  simpa only [Nat.add_comm n 1] using h.trans hrest

/-- The final nonempty iteration costs one pop plus the body. -/
theorem popLoop_stop {b : Bool} (hstack : s k = b :: tail) (hrep : repeatOn b = false)
    (hbody : if b then high.Runs n (Function.update s k tail) out
      else low.Runs n (Function.update s k tail) out) :
    (popLoop k repeatOn low high).Runs (1 + n) s out := by
  simpa only [hrep, Bool.false_eq_true, ite_false, Nat.add_comm n 1] using
    popLoop_body k repeatOn low high hstack hbody

theorem popLoop_false_continue (hstack : s k = false :: tail) (hrep : repeatOn false = true)
    (hbody : low.Runs n (Function.update s k tail) mid)
    (hrest : (popLoop k repeatOn low high).Runs m mid out) :
    (popLoop k repeatOn low high).Runs (1 + n + m) s out :=
  popLoop_continue k repeatOn low high hstack hrep hbody hrest

theorem popLoop_true_continue (hstack : s k = true :: tail) (hrep : repeatOn true = true)
    (hbody : high.Runs n (Function.update s k tail) mid)
    (hrest : (popLoop k repeatOn low high).Runs m mid out) :
    (popLoop k repeatOn low high).Runs (1 + n + m) s out :=
  popLoop_continue k repeatOn low high hstack hrep hbody hrest

theorem popLoop_false_stop (hstack : s k = false :: tail) (hrep : repeatOn false = false)
    (hbody : low.Runs n (Function.update s k tail) out) :
    (popLoop k repeatOn low high).Runs (1 + n) s out :=
  popLoop_stop k repeatOn low high hstack hrep hbody

theorem popLoop_true_stop (hstack : s k = true :: tail) (hrep : repeatOn true = false)
    (hbody : high.Runs n (Function.update s k tail) out) :
    (popLoop k repeatOn low high).Runs (1 + n) s out :=
  popLoop_stop k repeatOn low high hstack hrep hbody

end RAMTape.Routine.Runs

end VPVNP
end Computability
end OAI
