import OAI.Computability.IntegerMultiplication.SM.Stack

/-!
# Space accounting for a sequence of short stack-machine calls

One transition adds at most one letter to each stack. A computation split at
configurations where the stacks are small therefore has a space bound from
the largest single call, regardless of how many calls precede it.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Schoolbook

open IntegerMultiplication

variable {A Q I : Type} {m : SM.Rule A Q I}

/-- A stack-height cap throughout an actual run, including both endpoints. -/
structure Segment (m : SM.Rule A Q I) (x : SM.Config A Q I) (ticks : ℕ)
    (y : SM.Config A Q I) (capacity : ℕ) : Prop where
  run : Trace (SM.advance m) x ticks y
  height : ∀ {k u}, k ≤ ticks → Trace (SM.advance m) x k u →
    ∀ j, (u.stack j).length ≤ capacity

private theorem stack_growth {x y : SM.Config A Q I} {t : ℕ}
    (h : Trace (SM.advance m) x t y) (j : I) :
    (y.stack j).length ≤ (x.stack j).length + t := by
  induction h with
  | nil => simp
  | @cons x u y n h _ ih =>
    cases a : m x.pc (SM.tops x) with
    | none => simp [SM.advance, a] at h
    | some acts =>
      simp only [SM.advance, a, Option.map_some, Option.some.injEq] at h
      subst u
      have hs : ((SM.perform x acts).stack j).length ≤ (x.stack j).length + 1 := by
        change ((acts.2 j).perform (x.stack j)).length ≤ _
        cases acts.2 j <;> simp [SM.Action.perform]
        omega
      omega

/-- A time bound on an individual call bounds every intermediate height. -/
theorem Segment.of_cost {x y : SM.Config A Q I} {t H B : ℕ}
    (run : Trace (SM.advance m) x t y)
    (start : ∀ j, (x.stack j).length ≤ H) (cost : t ≤ B) :
    Segment m x t y (H+B) := by
  refine ⟨run, fun {k u} hk h j => ?_⟩
  have := stack_growth h j
  have := start j
  omega

theorem Segment.mono {x y : SM.Config A Q I} {t H H' : ℕ}
    (s : Segment m x t y H) (bound : H ≤ H') : Segment m x t y H' :=
  ⟨s.run, fun hk h j => (s.height hk h j).trans bound⟩

private theorem trace_drop {X : Type*} {s : X → Option X} {x y z : X} {n t : ℕ}
    (h : Trace s x n y) (h' : Trace s x t z) (hn : n ≤ t) : Trace s y (t-n) z := by
  induction h generalizing t with
  | nil => simpa using h'
  | @cons x u y n hx _ ih =>
    cases h' with
    | nil => omega
    | @cons _ v _ t hx' h' =>
      have e : u = v := Option.some.inj (hx.symm.trans hx')
      subst v
      rw [show 1+t-(1+n) = t-n by omega]; exact ih h' (by omega)

theorem Segment.trans {x y z : SM.Config A Q I} {t t' H : ℕ}
    (s : Segment m x t y H) (s' : Segment m y t' z H) : Segment m x (t+t') z H := by
  refine ⟨s.run.trans s'.run, fun {k u} hk h j => ?_⟩
  by_cases h₁ : k ≤ t
  · exact s.height h₁ h j
  · exact s'.height (show k-t ≤ t' by omega) (trace_drop s.run h (by omega)) j

/-- A sequence of calls with a common cost and space bound. -/
theorem segments_iterate {H B : ℕ} {state : ℕ → SM.Config A Q I} (n : ℕ)
    (start : ∀ j, ((state 0).stack j).length ≤ H)
    (step : ∀ i < n, ∃ t ≤ B, Segment m (state i) t (state (i+1)) H) :
    ∃ t ≤ n*B, Segment m (state 0) t (state n) H := by
  induction n with
  | zero =>
    refine ⟨0, by simp, (Segment.of_cost (Trace.nil _) start le_rfl).mono (by simp)⟩
  | succ n ih =>
    obtain ⟨t, ht, s⟩ := ih (fun i hi => step i (by omega))
    obtain ⟨t', ht', s'⟩ := step n (by omega)
    exact ⟨t+t', by rw [Nat.succ_mul]; omega, s.trans s'⟩

end Schoolbook

end NearSquareRoot
end Computability
end OAI
