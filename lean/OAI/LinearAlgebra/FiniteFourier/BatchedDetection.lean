import OAI.LinearAlgebra.FiniteFourier.BatchedGramValue
import OAI.LinearAlgebra.FiniteFourier.BatchedListPrice
import Mathlib.Tactic

/-! # Quantitative detection of a high-rank projection of the doubled list -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical NNReal Matrix

private theorem gram_ratio_bound :
    (181/50 : ℝ) ^ (51/100 : ℝ) ≤ 193/100 := by
  apply le_of_pow_le_pow_left₀ (by decide : (100:ℕ) ≠ 0) (by norm_num : (0:ℝ) ≤ 193/100)
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 181/50)]
  norm_num

private theorem large_list_of_paired_logs {n δ Δ u v g : ℝ}
    (hn : 0 < n) (hd : 0 < δ) (hD : 0 < Δ) (hratio : δ / Δ ≤ 51/100)
    (hgap : 5 * Δ ≤ (2*δ - Δ) * Real.logb 2 n)
    (hu : 0 < u) (hv : 0 < v) (hvmax : v ≤ 2*n)
    (hpair : Δ * Real.logb 2 g ≤ δ * Real.logb 2 u + δ * Real.logb 2 v)
    (hgram : 2 * (2:ℝ) ^ (2*δ * Real.logb 2 n / Δ) ≤ g + 2*n) :
    181/100*n ≤ u := by
  let F := (2:ℝ) ^ (2*δ * Real.logb 2 n / Δ)
  have hf : 32*n ≤ F := by
    have he : 5 + Real.logb 2 n ≤ 2*δ * Real.logb 2 n / Δ :=
      (le_div_iff₀ hD).mpr (by nlinarith)
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) he
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_logb (by norm_num) (by norm_num) hn] at h
    norm_num at h
    exact h
  by_contra! hsmall
  have hgpos : 0 < g := by unfold F at hf; linarith
  have huv : u*v ≤ (181/50)*n*n := by
    nlinarith [mul_le_mul_of_nonneg_left hvmax hu.le, mul_lt_mul_of_pos_right hsmall hn]
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) (mul_pos hu hv) huv
  rw [Real.logb_mul hu.ne' hv.ne', Real.logb_mul (by positivity) hn.ne',
    Real.logb_mul (by norm_num) hn.ne'] at hlog
  have hexp : Real.logb 2 g ≤ δ / Δ * Real.logb 2 (181/50) + 2*δ * Real.logb 2 n / Δ := by
    rw [div_mul_eq_mul_div, ← add_div]
    exact (le_div_iff₀ hD).mpr (by nlinarith [mul_le_mul_of_nonneg_left hlog hd.le])
  have hpow := (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2) hgpos).mp hexp
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)] at hpow
  have hrat : (2:ℝ) ^ (δ / Δ * Real.logb 2 (181/50)) ≤ 193/100 := by
    rw [← Real.logb_rpow_eq_mul_logb_of_pos (by norm_num : (0:ℝ) < 181/50),
      Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 181/50) hratio).trans gram_ratio_bound
  have hupper : g ≤ 193/100 * F := hpow.trans (mul_le_mul_of_nonneg_right hrat (by positivity))
  unfold F at *
  linarith

variable {K : Type*} [Field K] {R C : Type} [Fintype R] [Fintype C]

theorem listRaw_coeff_ne_zero {U : Matrix R C K} : (listRaw U).coeff ≠ 0 ↔ U ≠ 0 := by
  apply not_congr
  constructor
  · intro h
    ext i j
    have he := congrFun h (listCoordinates i j j)
    change (if j = j then U i j else 0) = 0 at he
    simpa using he
  · rintro rfl
    funext z
    change (if (z 1 : C) = z 2 then (0 : K) else 0) = 0
    exact ite_self _

variable (P : SpectralPlacementPrices K Plane)
    (φ χ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop))
    (ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 4) K → _ → Prop))

theorem full_list_detection [Nonempty R] [DecidableEq R]
    {x a b c d : Plane} {δ Δ : ℝ}
    (hl : PricesListsAt P φ x a b δ) (hr : PricesListsAt P χ x c d δ)
    (hrect : ∀ (I : Type) [Fintype I] (M : Matrix I I K),
      fourierPhasePrice P M ![a,c,b,d] = Δ * Real.logb 2 (phasePointValue ψ M))
    (hd : 0 < δ) (hD : 0 < Δ) (hratio : δ / Δ ≤ 51/100)
    (hgap : 5 * Δ ≤ (2*δ - Δ) * Real.logb 2 (Fintype.card R))
    (H : Matrix R R K) (hs : Hᵀ = H)
    (f : R → R) (hf : ∀ i j, j ≠ f i → (Hᵀ * H) i j = 0)
    (hsat : phasePointValue ψ H = (2:ℝ) ^ (2*δ * Real.logb 2 (Fintype.card R) / Δ)) :
    (181/100 : ℝ) * Fintype.card R ≤ listValue φ (Matrix.fromCols (1 : Matrix R R K) H) := by
  let U := Matrix.fromCols (1 : Matrix R R K) H
  let V := Matrix.fromCols H (1 : Matrix R R K)
  let i := Classical.arbitrary R
  have hu : (listRaw U).coeff ≠ 0 := listRaw_coeff_ne_zero.mpr (by
    intro h; simpa [U] using congrFun (congrFun h i) (.inl i))
  have hv : (listRaw V).coeff ≠ 0 := listRaw_coeff_ne_zero.mpr (by
    intro h; simpa [V] using congrFun (congrFun h i) (.inr i))
  have hpair := paired_list_price_le P U V hu hv a b c d x
  rw [hrect, hl R (R ⊕ R) U, hr R (R ⊕ R) V] at hpair
  have hgram := paired_augmented_phase_bound ψ H hs f hf
  rw [hsat] at hgram
  apply large_list_of_paired_logs (by positivity) hd hD hratio hgap _ _ _ hpair hgram
  · exact_mod_cast zero_lt_one.trans_le (one_le_raw_spectralValue φ _ hu)
  · exact_mod_cast zero_lt_one.trans_le (one_le_raw_spectralValue χ _ hv)
  · simpa [two_mul] using NNReal.coe_le_coe.mpr (listValue_le_columns χ V)

theorem projected_list_detection [Nonempty R] [DecidableEq R]
    (hflat : ∀ (s : Finset Plane) (hs : s.Nonempty), P.diagonal s = meanWidth s hs)
    {x a b hub : Plane} {δ τ : ℝ}
    (hl : PricesListsAt P φ x a b δ) (hd : 0 < δ) (hd' : δ ≤ 1)
    (hτ : (dist hub a + dist hub b + dist a b) / 2 = τ) (ht : τ ≤ 1)
    (hhub : dist x hub = 1/4)
    (hexcess : (τ + 1/4 - δ) * Real.logb 2 (Fintype.card R) ≤ 11)
    (H Q : Matrix R R K)
    (hfull : (181/100 : ℝ) * Fintype.card R ≤
      listValue φ (Matrix.fromCols (1 : Matrix R R K) H))
    (hQ : ((Fintype.card R - Q.rank : ℕ) : ℝ) ≤
      (2:ℝ) ^ (-(100:ℤ)) * Fintype.card R) :
    (9/5 : ℝ) * Fintype.card R ≤ listValue φ (Q * Matrix.fromCols (1 : Matrix R R K) H) := by
  let U := Matrix.fromCols (1 : Matrix R R K) H
  obtain ⟨W, _, hr, hv⟩ := exists_low_rank_list_remainder φ Q U
  have hn : (0:ℝ) < Fintype.card R := by positivity
  have hw : (listValue φ W : ℝ) ≤ (Fintype.card R : ℝ) / 128 := by
    by_cases hz : W = 0
    · rw [hz, listValue_zero, NNReal.coe_zero]
      positivity
    have hrpos : 0 < W.rank := by
      by_contra! he
      have hbot := Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero he :
        Module.finrank K (LinearMap.range W.mulVecLin) = 0)
      apply hz
      apply Matrix.toLin'.injective
      rw [map_zero]
      exact LinearMap.range_eq_bot.mp hbot
    have hrle : (W.rank : ℝ) ≤ (Fintype.card R : ℝ) / 2^100 := by
      apply (show (W.rank : ℝ) ≤ ((Fintype.card R - Q.rank : ℕ) : ℝ) by exact_mod_cast (by omega :
        W.rank ≤ Fintype.card R - Q.rank)).trans
      simpa [zpow_neg, div_eq_inv_mul] using hQ
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
      (show (0:ℝ) < W.rank by positivity) hrle
    rw [Real.logb_div hn.ne' (by positivity), Real.logb_pow] at hlog
    simp only [Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2), mul_one] at hlog
    apply listValue_le_of_price_le P φ hl hd W (by positivity)
    apply (listPrice_rank_le P hflat W x a b hub).trans
    rw [hτ, hhub, Fintype.card_sum, Nat.cast_add, ← two_mul,
      Real.logb_mul (by norm_num) hn.ne', Real.logb_div hn.ne' (by norm_num)]
    have h128 : Real.logb 2 128 = 7 := by
      rw [show (128:ℝ) = 2^7 by norm_num, Real.logb_pow]
      norm_num
    rw [h128, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
    norm_num at hlog
    nlinarith
  have hval : (listValue φ U : ℝ) ≤ (listValue φ (Q * U) : ℝ) + listValue φ W :=
    NNReal.coe_le_coe.mpr hv
  change _ ≤ (listValue φ (Q * U) : ℝ)
  change _ ≤ (listValue φ U : ℝ) at hfull
  linarith

end FiniteFourier
end LinearAlgebra
end OAI
