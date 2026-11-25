import OAI.Computability.NearSquareRoot.Asymptotic
import OAI.Computability.NearSquareRoot.Schedule

/-!
# Worst-case time of one geometric schedule

The inputs at a given length form a finite type. The maximum is computed from
the same run-length function before a comparison candidate is chosen. Each
accuracy index selects a single candidate uniformly for all sufficiently
large inputs. The scheduler itself takes neither of those indices as input.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Schedule

open Filter

variable {X : ℕ → Type*} [∀ n, Fintype (X n)]

/-- The same length-dependent time majorant serves every pair of inputs. -/
noncomputable def worstTime (time : (n : ℕ) → X n → ℕ) (n : ℕ) : ℕ :=
  Finset.univ.sup (time n)

theorem le_worstTime (time : (n : ℕ) → X n → ℕ) (n : ℕ) (x : X n) :
    time n x ≤ worstTime time n := Finset.le_sup (Finset.mem_univ x)

/-- For each fixed `j`, one candidate succeeds on every sufficiently large
input within the indicated output-inclusive tick budget. The round costs and
the initial scan bound are absolute. A physical implementation can discharge
`hstop` by a trace to the first accepted answer. -/
theorem allEpsilonBounds_of_schedule {σ α : Type*}
    (tick : σ → Tick σ α) (start : (n : ℕ) → X n → ℕ → σ)
    (time : (n : ℕ) → X n → ℕ) (cost : (n : ℕ) → X n → ℕ → ℕ)
    (C D : ℕ)
    (hcost : ∀ n x s, cost n x s ≤ C * 2^s)
    (hstop : ∀ n x s,
      (through (fun i b => tryFor tick b (start n x i)) s).isSome →
      time n x ≤ D * (n + 1) + prefixCost (cost n x) s)
    (hfixed : ∀ j : ℕ, ∃ (i : ℕ) (H : ℝ), 0 ≤ H ∧
      ∀ᶠ n in atTop, ∀ x : X n, ∃ (t : ℕ) (v : α),
        tryFor tick t (start n x i) = some v ∧
        (t : ℝ) ≤ H * n * logScale n ^ ((1 : ℝ)/2 + 1/(j+2 : ℝ))) :
    AllEpsilonBounds (worstTime time) := by
  apply allEpsilonBounds_of_indexed
  intro j
  obtain ⟨i, H, hH, hsuccess⟩ := hfixed j
  let F : ℕ := 8*C*2^i
  let K : ℝ := (2*D + F*(H+1) + 1 : ℝ)
  have hK : 0 < K := by unfold K; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hsuccess, eventually_ge_atTop (1:ℕ), tendsto_logScale.eventually_ge_atTop 1]
    with n hxn hn hlog
  let w := logScale n^((1:ℝ)/2 + 1/(j+2:ℝ))
  have hw : 1 ≤ w := Real.one_le_rpow hlog (by positivity)
  have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hnw : 1 ≤ (n:ℝ)*w := one_le_mul_of_one_le_of_one_le hn' hw
  -- An input attaining the maximum need only be chosen when the input type
  -- is inhabited; taking the natural-number floor also covers an empty type.
  have hbound (x : X n) : (time n x : ℝ) ≤ K*n*w := by
    obtain ⟨t,v,hrun,ht⟩ := hxn x
    obtain ⟨s, hdone, hs⟩ := uniform_schedule_bound (hcost n x) hrun
    have htime := (hstop n x s hdone).trans (Nat.add_le_add_left hs _)
    change time n x ≤ D*(n+1) + F*(t+1) at htime
    have htime' : (time n x : ℝ) ≤ (D:ℝ)*(n+1) + F*(t+1) := by exact_mod_cast htime
    change (t:ℝ) ≤ H*n*w at ht
    have hplus : (t:ℝ)+1 ≤ (H+1)*(n*w) := by linarith
    have hnplus : (n:ℝ)+1 ≤ 2*(n*w) := by
      nlinarith [le_mul_of_one_le_right (Nat.cast_nonneg n) hw]
    calc
      (time n x : ℝ) ≤ (D:ℝ)*(n+1) + F*(t+1) := htime'
      _ ≤ D*(2*(n*w)) + F*((H+1)*(n*w)) := by gcongr
      _ ≤ K*n*w := by dsimp only [K]; nlinarith
  have hfloor : worstTime time n ≤ ⌊K*n*w⌋₊ := by
    exact Finset.sup_le fun x _ => Nat.le_floor (hbound x)
  exact (by exact_mod_cast hfloor : (worstTime time n : ℝ) ≤ ⌊K*n*w⌋₊).trans
    (Nat.floor_le (by positivity))

end Schedule

end NearSquareRoot
end Computability
end OAI
