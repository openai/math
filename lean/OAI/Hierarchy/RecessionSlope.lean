import Mathlib.Analysis.Convex.Slope
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith

namespace OAI
/-! # Recession slopes of convex prices on a real line -/

namespace Hierarchy

open Filter Set
open scoped Topology

/-- A linear upper bound on the positive ray makes its increasing secant slopes converge. -/
theorem exists_recession_slope {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (h0 : f 0 = 0)
    {C : ℝ} (upper : ∀ t, 0 < t → f t ≤ t * C) :
    ∃ L : ℝ, Tendsto (fun t : ℝ => f t / t) atTop (𝓝 L) := by
  let g (t : ℝ) := f (max 1 t) / (max 1 t)
  have pos (t : ℝ) : 0 < max 1 t := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have increasing : Monotone g := by
    intro x y h
    simpa only [g, h0, sub_zero] using
      hf.secant_mono (mem_univ (0 : ℝ)) (mem_univ (max 1 x)) (mem_univ (max 1 y))
        (pos x).ne' (pos y).ne' (max_le_max_left 1 h)
  have bounded : BddAbove (range g) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact (div_le_iff₀ (pos t)).mpr (by simpa only [mul_comm C] using upper _ (pos t))
  refine ⟨_, (tendsto_atTop_ciSup increasing bounded).congr' ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  simp only [g, max_eq_right ht]

private theorem exists_large_scale {d : ℝ} (hd : 0 < d) (B : ℝ) :
    ∃ t : ℝ, 1 < t ∧ B < t * d := by
  refine ⟨max 2 ((B+1)/d), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  exact lt_of_lt_of_le (by linarith : B < B+1) ((div_le_iff₀ hd).mp (le_max_right _ _))

/-- Convexity and a global upper bound force the prices at zero and one to agree. -/
theorem convex_bdd_eq {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) {C : ℝ}
    (upper : ∀ t, f t ≤ C) : f 1 = f 0 := by
  apply le_antisymm
  · by_contra! lt
    obtain ⟨t, ht, more⟩ := exists_large_scale (sub_pos.mpr lt) (C - f 0)
    have secant := hf.secant_mono_aux1 (mem_univ (0 : ℝ)) (mem_univ t) zero_lt_one ht
    nlinarith [upper t]
  · by_contra! lt
    obtain ⟨t, ht, more⟩ := exists_large_scale (sub_pos.mpr lt) (C - f 0)
    have secant := hf.secant_mono_aux1 (mem_univ (-t)) (mem_univ (1 : ℝ))
      (show -t < 0 by linarith) zero_lt_one
    nlinarith [upper (-t)]

end Hierarchy

end OAI
