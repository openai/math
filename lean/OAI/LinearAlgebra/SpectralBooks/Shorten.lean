import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-! # Moving the two crossing centers at smooth unit vectors

The shifted crossing supplies a lower bound on the larger of the two placement costs.
Testing it on small displacements gives the manuscript's squared dual norm inequality.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open Filter Topology
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The limiting cost inequality for two shifted crossing factorizations, with arbitrary
centers on the two cuts. Each displayed cost accounts for one half of its symmetric placement. -/
def ShiftedCrossingCost (E : Type*) [NormedAddCommGroup E] : Prop :=
  ∀ (x y : E), ‖x‖ = 1 → ‖y‖ = 1 → ∀ t u δ : ℝ, 0 < t → 0 < u →
    -(t ^ 2 + u ^ 2) < δ → δ < t ^ 2 + u ^ 2 → ∀ p m : E,
    t + u ≤ max (t * ‖x - p‖ + u * ‖y - p‖ + ‖p‖ * Real.sqrt (t ^ 2 + u ^ 2 + δ))
      (t * ‖x - m‖ + u * ‖-y - m‖ + ‖m‖ * Real.sqrt (t ^ 2 + u ^ 2 - δ))

private theorem exists_positive_direction (L : E →L[ℝ] ℝ) {r : ℝ}
    (hr : 0 ≤ r) (h : r < ‖L‖) : ∃ z : E, r * ‖z‖ < L z := by
  obtain ⟨z, hz⟩ := L.exists_mul_lt_of_lt_opNorm hr h
  rw [Real.norm_eq_abs, lt_abs] at hz
  rcases hz with h | h
  · exact ⟨z, h⟩
  · exact ⟨-z, by simpa using h⟩

private theorem eventually_cost_lt {x y z : E} {f g : E →L[ℝ] ℝ} {t u r : ℝ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hf : HasFDerivAt (‖·‖) f x) (hg : HasFDerivAt (‖·‖) g y)
    (hz : r * ‖z‖ < t * f z + u * g z) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      t * ‖x - ε • z‖ + u * ‖y - ε • z‖ + ‖ε • z‖ * r < t + u := by
  let cost (ε : ℝ) := t * ‖x - ε • z‖ + u * ‖y - ε • z‖ + ε * (‖z‖ * r)
  have dx : HasDerivAt (fun ε : ℝ => ‖x - ε • z‖) (-f z) 0 := by
    simpa [HasLineDerivAt, sub_eq_add_neg] using hf.hasLineDerivAt (-z)
  have dy : HasDerivAt (fun ε : ℝ => ‖y - ε • z‖) (-g z) 0 := by
    simpa [HasLineDerivAt, sub_eq_add_neg] using hg.hasLineDerivAt (-z)
  have hd : HasDerivAt cost (t * -f z + u * -g z + ‖z‖ * r) 0 := by
    simpa [cost, Pi.add_def] using ((dx.const_mul t).add (dy.const_mul u)).add
      ((hasDerivAt_id' (0 : ℝ)).mul_const (‖z‖ * r))
  have hs := hd.hasDerivWithinAt (s := Set.Ioi (0 : ℝ)) |>.limsup_slope_le'
    (Set.notMem_Ioi.mpr le_rfl) (show t * -f z + u * -g z + ‖z‖ * r < 0 by linarith)
  filter_upwards [hs, self_mem_nhdsWithin] with ε hε hpos
  have hp : 0 < ε := hpos
  rw [slope_def_field, sub_zero, div_lt_iff₀ hp, zero_mul, sub_lt_zero] at hε
  simpa [cost, norm_smul, Real.norm_eq_abs, abs_of_pos hp, mul_assoc, hx, hy] using hε

/-- Equation (crossing-dual) at the smooth unit vectors. A failed inequality provides
a single shift and directions along which both placement costs strictly decrease. -/
theorem ShiftedCrossingCost.smooth_dual {x y : E} {f g : E →L[ℝ] ℝ}
    (cost : ShiftedCrossingCost E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hf : HasFDerivAt (‖·‖) f x) (hg : HasFDerivAt (‖·‖) g y)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    ‖t • f + u • g‖ ^ 2 + ‖t • f - u • g‖ ^ 2 ≤ 2 * (t ^ 2 + u ^ 2) := by
  let A := ‖t • f + u • g‖
  let B := ‖t • f - u • g‖
  let S := t ^ 2 + u ^ 2
  have htf : ‖t • f‖ ≤ t := by
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos ht] using
      mul_le_mul_of_nonneg_left (hf.le_of_lipschitz lipschitzWith_one_norm) ht.le
  have hug : ‖u • g‖ ≤ u := by
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hu] using
      mul_le_mul_of_nonneg_left (hg.le_of_lipschitz lipschitzWith_one_norm) hu.le
  have hA : A ≤ t + u := (norm_add_le _ _).trans (add_le_add htf hug)
  have hB : B ≤ t + u := (norm_sub_le _ _).trans (add_le_add htf hug)
  have hA₀ : 0 ≤ A := norm_nonneg _
  have hB₀ : 0 ≤ B := norm_nonneg _
  have hA₂ : A ^ 2 ≤ 2 * S := by
    dsimp [S]; nlinarith [sq_le_sq' (by linarith : -(t + u) ≤ A) hA, sq_nonneg (t-u)]
  have hB₂ : B ^ 2 ≤ 2 * S := by
    dsimp [S]; nlinarith [sq_le_sq' (by linarith : -(t + u) ≤ B) hB, sq_nonneg (t-u)]
  change A ^ 2 + B ^ 2 ≤ 2 * S
  by_contra! hfail
  let δ := (A ^ 2 - B ^ 2) / 2
  have hmin : -S < δ := by dsimp [δ]; linarith
  have hmax : δ < S := by dsimp [δ]; linarith
  have hplus : Real.sqrt (S + δ) < A := by
    nlinarith [Real.sq_sqrt (show 0 ≤ S + δ by linarith), show S + δ < A ^ 2 by dsimp [δ]; linarith,
      Real.sqrt_nonneg (S + δ)]
  have hminus : Real.sqrt (S - δ) < B := by
    nlinarith [Real.sq_sqrt (show 0 ≤ S - δ by linarith), show S - δ < B ^ 2 by dsimp [δ]; linarith,
      Real.sqrt_nonneg (S - δ)]
  obtain ⟨p, hp⟩ := exists_positive_direction _ (Real.sqrt_nonneg _) hplus
  obtain ⟨m, hm⟩ := exists_positive_direction _ (Real.sqrt_nonneg _) hminus
  have hg' : HasFDerivAt (‖·‖) (-g) (-y) := by
    simpa using hg.hasFDerivAt_norm_smul_neg (show (-1 : ℝ) < 0 by norm_num)
  have ep := eventually_cost_lt hx hy hf hg (t := t) (u := u) (z := p) (by simpa using hp)
  have em := eventually_cost_lt hx (norm_neg y ▸ hy) hf hg' (t := t) (u := u) (z := m)
    (by simpa [sub_eq_add_neg] using hm)
  obtain ⟨ε, h₁, h₂⟩ := (ep.and em).exists
  exact (not_lt_of_ge (cost x y hx hy t u δ ht hu hmin hmax (ε • p) (ε • m)))
    (max_lt h₁ h₂)

end

end

end SpectralBooks
end LinearAlgebra
end OAI
