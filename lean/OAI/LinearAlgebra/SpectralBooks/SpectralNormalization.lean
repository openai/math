import OAI.LinearAlgebra.SpectralBooks.SubadditiveSpectralBound

/-! # Normalized spectral evaluations on a subset of sites

A multiplicative subadditive evaluation monotone under inclusion of summands
becomes additive after taking the reciprocal diagonal power. This gives the
normalization on a subset of positive diameter in the manuscript.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Finset
open scoped NNReal

variable {A : Type*} [CommSemiring A] (v : A →* ℝ≥0) {p : ℝ} (hp : 0 < p)
  (hnat : ∀ n : ℕ, 0 < n → v (n : A) = (n : ℝ≥0) ^ p)

/-- Reciprocal diagonal power on a subset of positive diagonal price. -/
noncomputable def normalizeSpectral (p : ℝ) : A →* ℝ≥0 := (NNReal.rpowMonoidHom p⁻¹).comp v

include hp hnat in
private theorem normalizeSpectral_natCast (n : ℕ) (hn : 0 < n) :
    normalizeSpectral v p (n : A) = (n : ℝ≥0) := by
  change v (n : A) ^ p⁻¹ = _
  rw [hnat n hn, ← NNReal.rpow_mul, mul_inv_cancel₀ hp.ne', NNReal.rpow_one]

include hp hnat in
/-- The reciprocal power of a multiplicative, subadditive evaluation whose
value increases on adjoining direct summands is additive. -/
theorem normalizeSpectral_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    (hadd : ∀ x y, v (x + y) ≤ v x + v y) (hsub : ∀ x y, v x ≤ v (x + y)) (x : ι → A) :
    normalizeSpectral v p (∑ i, x i) = ∑ i, normalizeSpectral v p (x i) := by
  classical
  let w := normalizeSpectral v p
  let a := ∑ i, x i
  let b := ∑ i, w (x i)
  have hw (z : A) : w z ^ p = v z := by
    change (v z ^ p⁻¹) ^ p = v z
    rw [← NNReal.rpow_mul, inv_mul_cancel₀ hp.ne', NNReal.rpow_one]
  have hpow (m : ℕ) : v a ^ m ≤ ((m : ℝ≥0) + 1) ^ Fintype.card ι * (b ^ p)^m ∧
      b^m ≤ ((m : ℝ≥0) + 1) ^ Fintype.card ι * (w a)^m := by
    let J := (univ : Finset ι).piAntidiag m
    let t (k : ι → ℕ) : A := (Nat.multinomial univ k : A) * ∏ i, (x i)^(k i)
    have ha : a ^ m = ∑ k ∈ J, t k := Finset.sum_pow_eq_sum_piAntidiag univ x m
    have hb : b ^ m = ∑ k ∈ J, w (t k) := by
      dsimp only [b]
      rw [Finset.sum_pow_eq_sum_piAntidiag]
      apply Finset.sum_congr rfl
      intro k _
      simp only [t, map_mul, map_prod, map_pow]
      rw [show w (Nat.multinomial univ k : A) = (Nat.multinomial univ k : ℝ≥0) from
        normalizeSpectral_natCast v hp hnat _ (Nat.multinomial_pos univ k)]
    have hcard : (J.card : ℝ≥0) ≤ ((m : ℝ≥0) + 1)^Fintype.card ι := by
      exact_mod_cast degreeProfiles_card_le (ι := ι) m
    constructor
    · have hterm (k : ι → ℕ) (hk : k ∈ J) : v (t k) ≤ (b ^ p)^m := by
        rw [← hw, ← NNReal.rpow_mul_natCast, mul_comm p (m : ℝ), NNReal.rpow_natCast_mul]
        apply NNReal.rpow_le_rpow _ hp.le
        rw [hb]
        exact Finset.single_le_sum (f := fun j => w (t j)) (fun _ _ => by positivity) hk
      rw [← map_pow, ha]
      calc
        v (∑ k ∈ J, t k) ≤ ∑ k ∈ J, v (t k) :=
          Finset.le_sum_nonempty_of_subadditive v hadd (degreeProfiles_nonempty m) t
        _ ≤ ∑ _k ∈ J, (b^p)^m := sum_le_sum hterm
        _ = (J.card : ℝ≥0) * (b^p)^m := by simp
        _ ≤ _ := by gcongr
    · have hterm (k : ι → ℕ) (hk : k ∈ J) : w (t k) ≤ (w a)^m := by
        rw [← map_pow, ha, ← J.add_sum_erase t hk]
        exact NNReal.rpow_le_rpow (hsub _ _) (inv_nonneg.mpr hp.le)
      rw [hb]
      calc
        ∑ k ∈ J, w (t k) ≤ ∑ _k ∈ J, (w a)^m := sum_le_sum hterm
        _ = (J.card : ℝ≥0) * (w a)^m := by simp
        _ ≤ _ := by gcongr
  change w a = b
  apply le_antisymm
  · apply (NNReal.rpow_le_rpow_iff hp).mp
    rw [hw]
    exact nnreal_le_of_pow_le_polynomial_mul_pow _ fun m _ => (hpow m).1
  · exact nnreal_le_of_pow_le_polynomial_mul_pow _ fun m _ => (hpow m).2

include hp hnat in
/-- Normalization produces the semiring homomorphism of the restricted
spectrum when the evaluation vanishes at zero. -/
noncomputable def normalizeSpectralHom (hzero : v 0 = 0)
    (hadd : ∀ x y, v (x + y) ≤ v x + v y) (hsub : ∀ x y, v x ≤ v (x + y)) : A →+* ℝ≥0 where
  __ := normalizeSpectral v p
  map_zero' := by
    change v 0 ^ p⁻¹ = 0
    rw [hzero, NNReal.zero_rpow (inv_ne_zero hp.ne')]
  map_add' a b := by
    simpa [Fin.sum_univ_two] using normalizeSpectral_sum v hp hnat hadd hsub ![a, b]

end SpectralBooks
end LinearAlgebra
end OAI
