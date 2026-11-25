import OAI.Computability.NearSquareRoot.KernelPassMixValue
import OAI.Computability.NearSquareRoot.KernelPassMixError
import OAI.Computability.NearSquareRoot.PrecisionDiagonal

/-! # Euclidean accuracy and gain of a pointwise row mix

All addresses share a fixed matrix on row indices. Its Euclidean gain depends
only on that fixed matrix. Each output record incurs one truncation error.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPassMix

open IntegerMultiplication KernelPass Matrix Finset
open scoped BigOperators

variable {i o A h : ℕ}

/-- Stored output of a single pointwise row mix, using one common-denominator shift. -/
def roundedMix (w : ℕ) (c : Fin o → Fin i → Coefficient)
    (x : Fin i × Addr A h → Dusk.Grain w) (byAddr : Fin o × Addr A h) : Dusk.Grain w :=
  Grid.wrapMap w (Grid.divA (denom (c byAddr.1))
    (accum (c byAddr.1) (Grid.aspect ∘ (fun j => x (j, byAddr.2)))))

/-- The distance to the interpreted complex template result from represented inputs.
The only dimension-dependent factor is the square root of the number of rounded records. -/
theorem round_mix_error (p w : ℕ) (c : Fin o → Fin i → Coefficient)
    (x : Fin i × Addr A h → Dusk.Grain w)
    (fits : ∀ (b : Fin o) (y : Addr A h),
      ‖Grid.toC (accum (c b) (Grid.aspect ∘ (fun j => x (j,y)))) / (2 : ℂ)^denom (c b)‖ <
      (2 : ℝ)^w) :
    ‖(WithLp.toLp 2 (Grid.meaning p w ∘ roundedMix w c x) -
      WithLp.toLp 2 ((((Plan.mix (A := A) c).eval h).map (fun a => (a : ℂ))) *ᵥ
        (Grid.meaning p w ∘ x)) : EuclideanSpace ℂ (Fin o × Addr A h))‖ ≤
      Real.sqrt (Fintype.card (Fin o × Addr A h)) * ((2 : ℝ)/2^p) := by
  apply euclidean_norm_le_of_coordinates _ (by positivity)
  rintro ⟨b,y⟩
  change ‖Grid.meaning p w (roundedMix w c x (b,y)) -
    ((((Plan.mix (A := A) c).eval h).map (fun a => (a : ℂ))) *ᵥ (Grid.meaning p w ∘ x)) (b,y)‖ ≤ _
  rw [mix_complex_mulVec]
  change ‖Grid.meaning p w _ - ∑ j, (value (c b j) : ℂ) * Grid.meaning p w (x (j,y))‖ ≤ _
  rw [← accum_meaning]
  exact round_error p _ _ _ (fits b y)

/-- The squared Frobenius norm of the row matrix controls the full pass at
every address width, including when the number of output rows is zero. -/
theorem mix_norm_sq (c : Fin o → Fin i → Coefficient)
    (x : EuclideanSpace ℂ (Fin i × Addr A h)) :
    ‖(WithLp.toLp 2 ((((Plan.mix (A := A) c).eval h).map (fun a => (a : ℂ))) *ᵥ
      (fun t => x t)) : EuclideanSpace ℂ (Fin o × Addr A h))‖^2 ≤
      (∑ b, ∑ j, ‖(value (c b j) : ℂ)‖^2) * ‖x‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type]
  change (∑ b, ∑ y, ‖((((Plan.mix (A := A) c).eval h).map (fun a => (a : ℂ))) *ᵥ
    (fun t => x t)) (b,y)‖ ^ 2) ≤ _
  simp_rw [mix_complex_mulVec]
  let l (b : Fin o) := ∑ j, ‖(value (c b j) : ℂ)‖^2
  let e (y : Addr A h) := ∑ j, ‖x (j,y)‖^2
  have entry (b : Fin o) (y : Addr A h) :
      ‖∑ j, (value (c b j) : ℂ) * x (j,y)‖^2 ≤ l b * e y := by
    calc
      _ ≤ (∑ j, ‖(value (c b j) : ℂ) * x (j,y)‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ = (∑ j, ‖(value (c b j) : ℂ)‖ * ‖x (j,y)‖)^2 := by simp only [norm_mul]
      _ ≤ _ := sum_mul_sq_le_sq_mul_sq _ _ _
  calc
    _ ≤ ∑ b, ∑ y, l b * e y := sum_le_sum fun b _ => sum_le_sum fun y _ => entry b y
    _ = (∑ b, l b) * (∑ y, e y) := by simp_rw [← mul_sum]; rw [sum_mul]
    _ = _ := by congr 1; apply sum_comm

/-- An integer gain determined by the numerators of the fixed coefficient table. -/
def gain (c : Fin o → Fin i → Coefficient) : ℕ :=
  1 + ∑ b, ∑ j, (c b j).1.natAbs ^ 2

/-- The linear row-mix action with the Euclidean norm on all records together. -/
noncomputable def mixMap (c : Fin o → Fin i → Coefficient)
    (x : EuclideanSpace ℂ (Fin i × Addr A h)) : EuclideanSpace ℂ (Fin o × Addr A h) :=
  WithLp.toLp 2 ((((Plan.mix (A := A) c).eval h).map (fun a => (a : ℂ))) *ᵥ x.ofLp)

theorem gain_bound (c : Fin o → Fin i → Coefficient)
    (x : EuclideanSpace ℂ (Fin i × Addr A h)) : ‖mixMap c x‖ ≤ gain c * ‖x‖ := by
  have hcoef (a : Coefficient) : ‖(value a : ℂ)‖ ≤ (a.1.natAbs : ℝ) := by
    rw [value]
    push_cast
    simp only [norm_div, Complex.norm_intCast, norm_pow]
    rw [Complex.norm_ofNat, div_le_iff₀ (by positivity)]
    simpa using le_mul_of_one_le_right (abs_nonneg (a.1 : ℝ))
      (one_le_pow₀ (show 1 ≤ ‖(2:ℂ)‖ by norm_num) : 1 ≤ ‖(2:ℂ)‖^a.2)
  have coefficients : (∑ b, ∑ j, ‖(value (c b j) : ℂ)‖^2) ≤ (gain c : ℝ)^2 := by
    calc
      _ ≤ ∑ b, ∑ j, ((c b j).1.natAbs : ℝ)^2 := sum_le_sum fun b _ =>
        sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hcoef _) _
      _ ≤ _ := by
        exact_mod_cast (show (∑ b, ∑ j, (c b j).1.natAbs ^ 2) ≤ gain c ^ 2 by
          unfold gain
          nlinarith only [Nat.zero_le (∑ b, ∑ j, (c b j).1.natAbs ^ 2)])
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow]
  exact (mix_norm_sq c x).trans (mul_le_mul_of_nonneg_right coefficients (sq_nonneg _))

/-- One global bound suffices to fit every output of a fixed mix. -/
theorem mix_fits_of_norm (p w : ℕ) (c : Fin o → Fin i → Coefficient)
    (x : Fin i × Addr A h → Dusk.Grain w) (M : ℝ)
    (hb : ‖(WithLp.toLp 2 (Grid.meaning p w ∘ x) : EuclideanSpace ℂ _)‖ ≤ M)
    (hw : (gain c : ℝ) * M * 2^p < 2^w) (b : Fin o) (y : Addr A h) :
    ‖Grid.toC (accum (c b) (Grid.aspect ∘ (fun j => x (j,y)))) / (2 : ℂ)^denom (c b)‖ <
      (2 : ℝ)^w := by
  let v : EuclideanSpace ℂ (Fin i × Addr A h) := WithLp.toLp 2 (Grid.meaning p w ∘ x)
  have coord : ‖(mixMap c v) (b,y)‖ ≤ (gain c : ℝ) * M :=
    ((PiLp.norm_apply_le (mixMap c v) (b,y)).trans (gain_bound c v)).trans
      (mul_le_mul_of_nonneg_left hb (by positivity))
  change ‖((((Plan.mix (A := A) c).eval h).map (fun a => (a : ℂ))) *ᵥ
    fun z => Grid.meaning p w (x z)) (b,y)‖ ≤ _ at coord
  rw [← accum_eq_mix, norm_div] at coord
  simp only [norm_pow, Complex.norm_ofNat] at coord
  exact ((div_le_iff₀ (by positivity)).mp coord).trans_lt hw

/-- Rounding error and propagated input error for the full pointwise mixing pass. -/
theorem round_mix_perturbed (p w : ℕ) (c : Fin o → Fin i → Coefficient)
    (x : Fin i × Addr A h → Dusk.Grain w) (u : EuclideanSpace ℂ (Fin i × Addr A h))
    (M : ℝ) (hb : ‖(WithLp.toLp 2 (Grid.meaning p w ∘ x) : EuclideanSpace ℂ _)‖ ≤ M)
    (hw : (gain c : ℝ) * M * 2^p < 2^w) :
    ‖WithLp.toLp 2 (Grid.meaning p w ∘ roundedMix w c x) - mixMap c u‖ ≤
      Real.sqrt (Fintype.card (Fin o × Addr A h)) * ((2 : ℝ)/2^p) +
        gain c * ‖WithLp.toLp 2 (Grid.meaning p w ∘ x) - u‖ := by
  let v : EuclideanSpace ℂ (Fin i × Addr A h) := WithLp.toLp 2 (Grid.meaning p w ∘ x)
  have sub : mixMap c (v-u) = mixMap c v - mixMap c u := by
    unfold mixMap
    simp only [WithLp.ofLp_sub, Matrix.mulVec_sub, WithLp.toLp_sub]
  calc
    _ ≤ _ := norm_sub_le_norm_sub_add_norm_sub _ (mixMap c v) _
    _ ≤ _ := add_le_add (round_mix_error p w c x (mix_fits_of_norm p w c x M hb hw))
      (sub ▸ gain_bound c (v-u))

end KernelPassMix

end NearSquareRoot
end Computability
end OAI
