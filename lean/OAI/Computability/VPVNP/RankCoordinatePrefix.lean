import OAI.Computability.VPVNP.RoutineSpace
import OAI.Computability.VPVNP.GreedySuffixIndex

/-! # Physical prefix scan for the greedy row and column indices of Appendix D.2

Each test queries the rank of the original matrix up to the current inclusive
row. The same controller works on the transposed selected-row matrix for the
column scan. Only a failed test increments the cursor. The returned cursor is
the zero-based original index.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate

open RAMTape UniversalCountStack

variable {K : Type}

/-- Finite controller for a rank test and a cursor increment. Both subroutine
returns redirect directly to the caller. -/
def greedyPrefix (flag : K) (test bump : FiniteRoutine K) : FiniteRoutine K :=
  .ofRoutine (Q := test.State ⊕ (Unit ⊕ bump.State)) {
    entry := .inl test.body.entry
    code := fun
      | .inl q => test.body.install Sum.inl (some (.inr (.inl ()))) q
      | .inr (.inl ()) => .pop flag (fun b => if b = some false then some (.inr (.inr bump.body.entry)) else none)
      | .inr (.inr q) => bump.body.install (Sum.inr ∘ Sum.inr) (some (.inl test.body.entry)) q }

variable [DecidableEq K]

/-- One iteration consumes the returned decision bit. When it is true, the
successful candidate stays in the cursor register. -/
private theorem testIteration {flag : K} {test bump : FiniteRoutine K} {cap n : ℕ}
    {s out : Stacks K} {b : Bool} (hflag : out flag = [])
    (run : test.BoundedRun cap n s (Function.update out flag [b])) :
    let scan := greedyPrefix flag test bump
    SpaceRun scan.body.standalone cap (n+1) (some scan.body.entry) s
      (if b = false then some (.inr (.inr bump.body.entry)) else none) out := by
  let scan := greedyPrefix flag test bump
  have installed := run.linkRoutine scan.body Sum.inl (some (.inr (.inl ()))) (fun _ ↦ rfl)
  have small (k : K) : (out k).length ≤ cap := by
    by_cases e : k = flag
    · simp [e, hflag]
    · simpa only [Function.update_of_ne e] using run.final_cap k
  have step := StackStep.pop (s := Function.update out flag [b])
    (show scan.body.standalone (some (.inr (.inl ()))) = .pop flag
      (fun bit => if bit = some false then some (.inr (.inr bump.body.entry)) else none) from rfl)
  have hup : Function.update out flag [] = out := by rw [← hflag, Function.update_eq_self]
  simp only [Function.update_self, List.head?_cons, List.tail_cons, Option.some.injEq,
    Function.update_idem, hup] at step
  exact installed.trans (.cons run.final_cap step (.nil _ _ small))

/-- With a first successful index `last`, bounded subcalls give a bounded
physical scan. The cap is independent of the number of preceding failed tests. -/
theorem first_test_runs {flag : K} (test bump : FiniteRoutine K) {cap T B last : ℕ}
    (input checked : ℕ → Stacks K) (hflag : ∀ j ≤ last, checked j flag = [])
    (htest : ∀ j ≤ last, ∃ t ≤ T, test.BoundedRun cap t (input j)
      (Function.update (checked j) flag [decide (j = last)]))
    (hbump : ∀ j < last, ∃ t ≤ B, bump.BoundedRun cap t (checked j) (input (j+1))) :
    ∃ t ≤ (last+1)*(T+1+B), (greedyPrefix flag test bump).BoundedRun cap t (input 0) (checked last) := by
  let scan := greedyPrefix flag test bump
  have loop (remaining j : ℕ) (hj : j+remaining=last) :
      ∃ t ≤ (remaining+1)*(T+1+B), scan.BoundedRun cap t (input j) (checked last) := by
    induction remaining generalizing j with
    | zero =>
      obtain ⟨a, ha, checkedRun⟩ := htest j (by omega)
      have run := testIteration (bump := bump) (hflag j (by omega)) checkedRun
      simp only [Nat.add_zero] at hj
      subst j
      refine ⟨a+1, by omega, ?_⟩
      simpa only [decide_true, Bool.true_eq_false, ite_false, scan] using run
    | succ r ih =>
      obtain ⟨a, ha, checkedRun⟩ := htest j (by omega)
      have run := testIteration (bump := bump) (hflag j (by omega)) checkedRun
      have hlt : j < last := by omega
      obtain ⟨b, hb, bumped⟩ := hbump j hlt
      have one : SpaceRun scan.body.standalone cap (a+1) (some scan.body.entry) (input j)
          (some (.inr (.inr bump.body.entry))) (checked j) := by
        simpa only [decide_eq_false hlt.ne, ite_true, scan] using run
      have next := bumped.linkRoutine scan.body (Sum.inr ∘ Sum.inr) (some scan.body.entry) (fun _ ↦ rfl)
      obtain ⟨c, hc, tail⟩ := ih (j+1) (by omega)
      refine ⟨_, ?_, (one.trans next).trans tail⟩
      rw [Nat.succ_mul]
      omega
  exact loop last 0 (Nat.zero_add _)

/-- The test contract refers to prefix ranks of the supplied matrix, not a basis
computed recursively. It also applies verbatim to column selection on a transpose. -/
theorem greedyPrefix_runs {F : Type*} [Field F] [DecidableEq F] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) F) (k : Fin (rankQuery A)) (flag : K) (test bump : FiniteRoutine K)
    {cap T B : ℕ} (input checked : ℕ → Stacks K) (hflag : ∀ j < n, checked j flag = [])
    (htest : ∀ j (hj : j < n), ∃ t ≤ T, test.BoundedRun cap t (input j)
      (Function.update (checked j) flag [decide (k.val < rankQuery (prefixRows A (j+1) hj))]))
    (hbump : ∀ j, j+1 < n → ∃ t ≤ B, bump.BoundedRun cap t (checked j) (input (j+1))) :
    ∃ t ≤ n*(T+1+B), (greedyPrefix flag test bump).BoundedRun cap t (input 0)
      (checked (greedyRowIndex A k).val) := by
  let last := (greedyRowIndex A k).val
  have fits : last < n := (greedyRowIndex A k).isLt
  have same (j : ℕ) (h : j ≤ last) (hj : j < n) : (k.val < rankQuery (prefixRows A (j+1) hj)) ↔ j = last := by
    rw [← greedyRowIndex_lt_iff]
    change last < j+1 ↔ j = last
    omega
  obtain ⟨t, ht, run⟩ := first_test_runs (last := last) (T := T) (B := B) test bump input checked
    (fun j hj ↦ hflag j (hj.trans_lt fits))
    (fun j hj ↦ by simpa only [same j hj (hj.trans_lt fits)] using htest j (hj.trans_lt fits))
    (fun j hj ↦ hbump j (by omega))
  exact ⟨t, ht.trans (Nat.mul_le_mul_right _ fits), run⟩

end RankQuery.Stack.Coordinate

end VPVNP
end Computability
end OAI
