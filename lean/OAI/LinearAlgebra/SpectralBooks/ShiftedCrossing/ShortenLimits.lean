import OAI.LinearAlgebra.SpectralBooks.Shorten
import OAI.LinearAlgebra.SpectralBooks.ShiftedCrossing.ShortenTensor

/-! # Passing to normalized rates in the shifted crossing

The two cuts can use different channels. Only upper bounds on their normalized
logarithms are needed. The additive price of the ordinary sum disappears after
division by the size parameter.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace ShiftedCrossing

open Filter Real
open scoped Topology

/-- The two wire dimensions converge at their prescribed logarithmic rates, while
the channel dimensions obey the shifted square-root bounds. -/
def AsymptoticFactorizations (K : Type*) [Field K] : Prop :=
  ∀ t u δ : ℝ, 0 < t → 0 < u → -(t ^ 2 + u ^ 2) < δ → δ < t ^ 2 + u ^ 2 →
    ∃ (dx dy rp rm : ℕ → ℕ) (bp bm : ℕ → ℝ),
      (∀ᶠ n in atTop, 0 < dx n ∧ 0 < dy n ∧ Nonempty (Factorization K (dx n) (dy n) (rp n) (rm n))) ∧
      Tendsto (fun n => logb 2 (dx n) / n) atTop (𝓝 t) ∧
      Tendsto (fun n => logb 2 (dy n) / n) atTop (𝓝 u) ∧
      (∀ᶠ n in atTop, logb 2 (rp n) / n ≤ bp n ∧ logb 2 (rm n) / n ≤ bm n) ∧
      Tendsto bp atTop (𝓝 (√(t ^ 2 + u ^ 2 + δ))) ∧
      Tendsto bm atTop (𝓝 (√(t ^ 2 + u ^ 2 - δ)))

/-- Normalizing a bound by the larger of the two finite cut costs preserves
the maximum in the limit, even if the winning cut changes with `n`. -/
theorem cost_limit {X Y Rp Rm Bp Bm : ℕ → ℝ}
    {t u bp bm xp yp dp xm ym dm C : ℝ} (hdp : 0 ≤ dp) (hdm : 0 ≤ dm)
    (hx : Tendsto (fun n => X n / n) atTop (𝓝 t)) (hy : Tendsto (fun n => Y n / n) atTop (𝓝 u))
    (hbp : Tendsto Bp atTop (𝓝 bp)) (hbm : Tendsto Bm atTop (𝓝 bm))
    (hr : ∀ᶠ n in atTop, Rp n / n ≤ Bp n ∧ Rm n / n ≤ Bm n)
    (hc : ∀ᶠ n in atTop, 2 * (X n + Y n) ≤
      max (2 * (X n * xp + Y n * yp + dp * Rp n))
        (2 * (X n * xm + Y n * ym + dm * Rm n)) + C) :
    t + u ≤ max (t * xp + u * yp + dp * bp) (t * xm + u * ym + dm * bm) := by
  have hp := ((hx.mul_const xp).add (hy.mul_const yp)).add (hbp.const_mul dp)
  have hm := ((hx.mul_const xm).add (hy.mul_const ym)).add (hbm.const_mul dm)
  have ho : Tendsto (fun n : ℕ => (C / 2) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply le_of_tendsto_of_tendsto (hx.add hy)
    (by simpa only [add_zero] using (hp.max hm).add ho)
  filter_upwards [hr, hc, eventually_gt_atTop 0] with n hrn hcn hn
  have hpos : 0 < (n : ℝ) := by exact_mod_cast hn
  change X n / n + Y n / n ≤
    max (X n / n * xp + Y n / n * yp + dp * Bp n)
      (X n / n * xm + Y n / n * ym + dm * Bm n) + (C / 2) / n
  let k : ℝ := (2 * (n : ℝ))⁻¹
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have h := mul_le_mul_of_nonneg_right hcn hk
  rw [add_mul, max_mul_of_nonneg _ _ hk] at h
  calc
    _ = 2 * (X n + Y n) * k := by dsimp [k]; field_simp
    _ ≤ _ := h
    _ = max (X n / n * xp + Y n / n * yp + dp * (Rp n / n))
         (X n / n * xm + Y n / n * ym + dm * (Rm n / n)) + (C / 2) / n := by
       dsimp [k]
       congr 1
       · congr 1 <;> field_simp
       · ring
    _ ≤ _ := by
       gcongr
       · exact hrn.1
       · exact hrn.2

end ShiftedCrossing

end

end SpectralBooks
end LinearAlgebra
end OAI
