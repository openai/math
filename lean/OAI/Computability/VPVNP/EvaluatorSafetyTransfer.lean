import OAI.Computability.VPVNP.EvaluatorRoutineSafety
import OAI.Computability.VPVNP.RoutineSpace

/-!
# Storage bounds for short branches and streamed queries

A short nondeterministic routine can increase a stack by at most its instruction
count. A deterministic long-running subroutine instead supplies the independent
peak bound along its actual run.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorRoutineSafety

open RAMTape UniversalCountStack

variable {K Q : Type*} [DecidableEq K] {r : Routine K Q}

/-- Add a reserved continuation clock and a peak bound to a short all-path
execution. Only the routine's own instruction count is charged to its storage. -/
theorem safe_of_allStops {safe : Stacks K → Prop} (cont : ℕ → Stacks K → Prop)
    {n : ℕ} (reserve : ℕ) {q : Option Q} {s : Stacks K}
    (h : r.AllStopsFrom (fun left out ↦ cont (reserve+left) out) n q s)
    (hroom : ∀ u, (∀ k, (u k).length ≤ (s k).length+n) → safe u) :
    r.SafeFrom safe cont (reserve+n) q s := by
  induction n generalizing q s with
  | zero =>
    cases q with
    | none => simpa only [Routine.safeFrom_none, Routine.allStopsFrom_none, Nat.add_zero] using h
    | some q => exact False.elim h
  | succ n ih =>
    cases q with
    | none => simpa only [Routine.safeFrom_none, Routine.allStopsFrom_none] using h
    | some q =>
      rw [Nat.add_succ, Routine.SafeFrom]
      refine ⟨hroom s (by intro k; omega), ?_⟩
      rw [Routine.AllStopsFrom] at h
      cases he : r.code q <;> rw [he] at h
      case push k b next =>
        apply ih h
        intro u hu
        apply hroom u
        intro j
        by_cases hj : j = k <;> simpa [hj] using (show _ ≤ _ from
          (hu j).trans (by simp [hj] <;> omega))
      case pop k next =>
        apply ih h
        intro u hu
        apply hroom u
        intro j
        by_cases hj : j = k <;> simpa [hj] using (show _ ≤ _ from
          (hu j).trans (by simp [hj] <;> omega))
      case goto =>
        exact ih h fun u hu ↦ hroom u fun k ↦ by have := hu k; omega
      case choose =>
        exact ⟨ih h.1 fun u hu ↦ hroom u fun k ↦ by have := hu k; omega,
          ih h.2 fun u hu ↦ hroom u fun k ↦ by have := hu k; omega⟩
      case halt => trivial

private theorem safe_of_space_run {cap n q s out} {cont : ℕ → Stacks K → Prop}
    (run : SpaceRun r.standalone cap n q s none out) (extra : ℕ) (hc : cont extra out) :
    r.SafeFrom (fun u ↦ ∀ k, (u k).length ≤ cap) cont (extra+n) q s := by
  generalize eq : (none : Option Q) = t at run
  induction run with
  | nil => rw [← eq]; simpa using hc
  | @cons q _ q' _ _ _ _ hs st _ ih =>
    cases q with
    | none => cases st <;> contradiction
    | some q =>
      cases st with
      | push h | pop h | goto h =>
        change r.code q = _ at h
        rw [Nat.add_succ, Routine.SafeFrom, h]
        exact ⟨hs, ih hc eq⟩

/-- A deterministic, space-bounded coordinate query satisfies the scheduler's
all-path contract even when the query time is exponential. -/
theorem Bounded.of_space_runs {S T : Type*} {pre : S → Stacks K} {post : T → Stacks K}
    {g : S → T} {B cap : ℕ} (run : ∀ x, ∃ n ≤ B,
      SpaceRun r.standalone cap n (some r.entry) (pre x) none (post (g x))) :
    Bounded r (fun u ↦ ∀ k, (u k).length ≤ cap) pre post B := by
  intro reserve fuel hf x cont hc
  obtain ⟨n, hn, hr⟩ := run x
  have h := safe_of_space_run hr (fuel-n) (hc _ _ (by omega))
  rwa [Nat.sub_add_cancel (by omega)] at h

end EvaluatorRoutineSafety

end VPVNP
end Computability
end OAI
