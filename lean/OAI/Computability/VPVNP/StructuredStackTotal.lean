import OAI.Computability.VPVNP.StructuredStackClock

/-!
# Bounding all branches of a structured stack program

The continuation receives the remaining fuel on each normal return. A direct
halt always finishes, including a rejecting halt. A binary choice satisfies
the bound exactly when both alternatives satisfy it.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Routine

variable {K Q R : Type*} [DecidableEq K]

/-- Every branch from the given local control halts or returns within the available fuel, with
each normal return satisfying the continuation at its remaining fuel and final stack bank. -/
def AllStopsFrom (r : Routine K Q) (cont : ℕ → Stacks K → Prop) :
    ℕ → Option Q → Stacks K → Prop
  | t, none, s => cont t s
  | 0, some _, _ => False
  | t+1, some q, s =>
    match r.code q with
    | .push k b next => r.AllStopsFrom cont t next (Function.update s k (b :: s k))
    | .pop k next => r.AllStopsFrom cont t (next (s k).head?) (Function.update s k (s k).tail)
    | .goto next => r.AllStopsFrom cont t next s
    | .choose a b => r.AllStopsFrom cont t a s ∧ r.AllStopsFrom cont t b s
    | .halt _ => True

/-- The all-branches termination condition for a routine started at its entry label, with the
continuation checked on each normal return. -/
abbrev AllStops (r : Routine K Q) (cont : ℕ → Stacks K → Prop) (n : ℕ) (s : Stacks K) :=
  r.AllStopsFrom cont n (some r.entry) s

@[simp] theorem allStopsFrom_none (r : Routine K Q) (c : ℕ → Stacks K → Prop)
    (t : ℕ) (s : Stacks K) : r.AllStopsFrom c t none s ↔ c t s := by cases t <;> rfl

theorem stopsWithin_close_iff (r : Routine K Q) (outcome : Bool) (t : ℕ) (q : Option Q)
    (s : Stacks K) :
    StopsWithin (r.close outcome) t q s ↔ r.AllStopsFrom (fun n _ => 0 < n) t q s := by
  induction t generalizing q s with
  | zero => cases q <;> simp [StopsWithin, AllStopsFrom]
  | succ t ih =>
    cases q with
    | none => simp [StopsWithin, AllStopsFrom, close]
    | some q =>
      simp only [StopsWithin, close, AllStopsFrom]
      cases r.code q <;> simp only [ih]

theorem allStopsFrom_install (outer : Routine K R) (inner : Routine K Q)
    (label : Q → R) (resume : Option R) (h : ∀ q, outer.code (label q) = inner.install label resume q)
    (c : ℕ → Stacks K → Prop) (t : ℕ) (q : Option Q) (s : Stacks K) :
    outer.AllStopsFrom c t (q.elim resume (some ∘ label)) s ↔
      inner.AllStopsFrom (fun n st => outer.AllStopsFrom c n resume st) t q s := by
  induction t generalizing q s with
  | zero => cases q <;> rfl
  | succ t ih =>
    cases q with
    | none => rfl
    | some q =>
      simp only [Option.elim_some, Function.comp_apply, AllStopsFrom, h, install]
      cases inner.code q <;> simp only [StackOp.rename, id_eq, Function.comp_apply, ih]

theorem allStops_followedBy (a : Routine K Q) (b : Routine K R) (c : ℕ → Stacks K → Prop)
    (t : ℕ) (s : Stacks K) :
    (a.followedBy b).AllStops c t s ↔ a.AllStops (b.AllStops c) t s := by
  have second (n : ℕ) (st : Stacks K) :
      (a.followedBy b).AllStopsFrom c n (some (.inr b.entry)) st ↔ b.AllStops c n st := by
    simpa only [Option.elim_some, Function.comp_apply, allStopsFrom_none] using
      allStopsFrom_install (a.followedBy b) b Sum.inr none (fun _ => rfl) c n (some b.entry) st
  change (a.followedBy b).AllStopsFrom c t (some (.inl a.entry)) s ↔
    a.AllStopsFrom (fun n st => b.AllStops c n st) t (some a.entry) s
  simpa only [Option.elim_some, Function.comp_apply, second] using
    allStopsFrom_install (a.followedBy b) a Sum.inl (some (.inr b.entry)) (fun _ => rfl)
      c t (some a.entry) s

/-- A deterministic successful run spends exactly its stated cost and hands every
remaining clock tick to the continuation. -/
theorem Runs.allStops_iff {r : Routine K Q} {n : ℕ} {s out : Stacks K} (h : r.Runs n s out)
    (cont : ℕ → Stacks K → Prop) (fuel : ℕ) :
    r.AllStops cont (fuel+n) s ↔ cont fuel out := by
  have aux {a : ℕ} {q q' : Option Q} {u v : Stacks K}
      (run : StackRuns r.standalone a q u q' v) :
      r.AllStopsFrom cont (fuel+a) q u ↔ r.AllStopsFrom cont fuel q' v := by
    induction run with
    | nil => rfl
    | @cons q u _ _ _ _ a hs _ ih =>
      cases q with
      | none => cases hs <;> contradiction
      | some q =>
        cases hs with
        | push he | pop he | goto he =>
          change r.code q = _ at he
          rw [show fuel + (a+1) = (fuel+a)+1 by omega, AllStopsFrom, he]
          exact ih
  simpa only [allStopsFrom_none] using aux h

end RAMTape.Routine

end VPVNP
end Computability
end OAI
