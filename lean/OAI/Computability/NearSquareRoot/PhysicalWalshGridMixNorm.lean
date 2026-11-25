import OAI.Computability.NearSquareRoot.PhysicalWalshGrid
import OAI.Computability.NearSquareRoot.KernelPassMixNorm

/-! # Accuracy and headroom of the physical mix on a finite row of records -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshGrid

open IntegerMultiplication PhysicalWalsh KernelPass KernelPassMix Finset
open scoped BigOperators

variable {a i o : ℕ} {U F J : Type} [Fintype J]

/-- A simultaneous bound on the absolute row sums of the fixed dyadic table. -/
def mixGain (c : Fin o → Fin i → Coefficient) : ℕ :=
  ∑ b, ∑ j, (c b j).1.natAbs

theorem row_sums_le (c : Fin o → Fin i → Coefficient) (b : Fin o) :
    (∑ j, ‖(value (c b j) : ℂ)‖) ≤ (mixGain c : ℝ) := by
  calc
    _ ≤ ∑ j, ((c b j).1.natAbs : ℝ) := sum_le_sum fun j _ => by
      rw [value]
      push_cast
      simp only [norm_div, Complex.norm_intCast, norm_pow, Complex.norm_ofNat]
      rw [div_le_iff₀ (by positivity)]
      simpa using le_mul_of_one_le_right (abs_nonneg ((c b j).1 : ℝ))
        (one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num) : 1 ≤ (2:ℝ)^(c b j).2)
    _ ≤ _ := by
      exact_mod_cast (Finset.single_le_sum (f := fun b => ∑ j, (c b j).1.natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))

/-- Ideal linear combination on whole Euclidean rows. -/
noncomputable def idealMixRow (c : Fin o → Fin i → Coefficient)
    (v : Fin i → EuclideanSpace ℂ J) (b : Fin o) : EuclideanSpace ℂ J :=
  ∑ j, (value (c b j) : ℂ) • v j

theorem idealMixRow_gain (c : Fin o → Fin i → Coefficient) (v : Fin i → EuclideanSpace ℂ J)
    (M : ℝ) (hM : 0 ≤ M) (hv : ∀ j, ‖v j‖ ≤ M) (b : Fin o) :
    ‖idealMixRow c v b‖ ≤ mixGain c * M := by
  calc
    _ ≤ ∑ j, ‖(value (c b j) : ℂ) • v j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖(value (c b j) : ℂ)‖ * M := sum_le_sum fun j _ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hv j) (norm_nonneg _)
    _ ≤ _ := by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (row_sums_le c b) hM

variable (L : KernelScaleBank.Layout a U F) (w : U → ℕ)

/-- Decode one selected finite row in its physical order. The same selector
may be used for the ordinal tape layout and for a prefix/suffix fibre. -/
noncomputable def decodeRow (p : ℕ) (u : U) (select : J → F) (x : (layout L w).Row u) : EuclideanSpace ℂ J :=
  WithLp.toLp 2 (fun t => Grid.meaning p (w u) (x (select t)))

private theorem entry_room (c : Fin o → Fin i → Coefficient) (p k : ℕ)
    (x : Fin i → Dusk.Grain k) (M : ℝ) (hM : 0 ≤ M)
    (hx : ∀ j, ‖Grid.meaning p k (x j)‖ ≤ M) (hw : (mixGain c : ℝ)*M*2^p < 2^k) (b : Fin o) :
    ‖Grid.toC (accum (c b) (Grid.aspect ∘ x)) / (2 : ℂ)^denom (c b)‖ < (2:ℝ)^k := by
  have e := accum_meaning (c b) p k x
  have h : ‖∑ j, (value (c b j) : ℂ) * Grid.meaning p k (x j)‖ ≤ mixGain c*M := by
    calc
      _ ≤ ∑ j, ‖(value (c b j) : ℂ) * Grid.meaning p k (x j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖(value (c b j) : ℂ)‖ * M := sum_le_sum fun j _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hx j) (norm_nonneg _)
      _ ≤ _ := by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (row_sums_le c b) hM
  rw [← e, norm_div, norm_pow, Complex.norm_ofNat] at h
  exact ((div_le_iff₀ (by positivity)).mp h).trans_lt hw

/-- The decoded pointwise input bound enforces the actual compiler guard. -/
theorem mixFits_of_pointwise (c : Fin o → Fin i → Coefficient) (p : ℕ)
    (u : U) (x : Rows (layout L w) u i) (M : ℝ) (hM : 0 ≤ M)
    (hx : ∀ z ∈ L.rows u, ∀ j, ‖Grid.meaning p (w u) (x j z)‖ ≤ M)
    (hw : (mixGain c : ℝ)*M*2^p < 2^(w u)) : mixFits L w c u x := by
  intro z hz b
  exact divA_fits _ _ _ (entry_room c p (w u) (fun j => x j z) M hM (hx z hz) hw b)

/-- A cover of the stored addresses transfers input row norms to the guard. -/
theorem mixFits_of_rows (c : Fin o → Fin i → Coefficient) (p : ℕ)
    (u : U) (select : J → F) (cover : ∀ z ∈ L.rows u, ∃ j, select j = z)
    (x : Rows (layout L w) u i) (M : ℝ) (hM : 0 ≤ M)
    (hx : ∀ j, ‖decodeRow L w p u select (x j)‖ ≤ M)
    (hw : (mixGain c : ℝ)*M*2^p < 2^(w u)) : mixFits L w c u x := by
  apply mixFits_of_pointwise L w c p u x M hM _ hw
  intro z hz j
  obtain ⟨t,rfl⟩ := cover z hz
  exact (PiLp.norm_apply_le (decodeRow L w p u select (x j)) t).trans (hx j)

theorem mix_row_round (c : Fin o → Fin i → Coefficient) (p : ℕ)
    (u : U) (select : J → F) (x : Rows (layout L w) u i) (M : ℝ) (hM : 0 ≤ M)
    (hx : ∀ j, ‖decodeRow L w p u select (x j)‖ ≤ M)
    (hw : (mixGain c : ℝ)*M*2^p < 2^(w u)) (b : Fin o) :
    ‖decodeRow L w p u select (mix L w c u x b) -
      idealMixRow c (fun j => decodeRow L w p u select (x j)) b‖ ≤
      Real.sqrt (Fintype.card J) * ((2:ℝ)/2^p) := by
  apply euclidean_norm_le_of_coordinates _ (by positivity)
  intro t
  have he := round_error p _ (w u) _ (entry_room c p (w u) (fun j => x j (select t)) M hM
    (fun j => (PiLp.norm_apply_le (decodeRow L w p u select (x j)) t).trans (hx j)) hw b)
  rw [accum_meaning] at he
  simpa [decodeRow, idealMixRow, mix, rounded, PiLp.sub_apply] using he

/-- One physical mix step propagates the maximal input lane error and adds
one complex fixed-point truncation per selected record. -/
theorem mix_row_error (c : Fin o → Fin i → Coefficient) (p : ℕ)
    (u : U) (select : J → F) (x : Rows (layout L w) u i) (v : Fin i → EuclideanSpace ℂ J)
    (M E : ℝ) (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hx : ∀ j, ‖decodeRow L w p u select (x j)‖ ≤ M)
    (herr : ∀ j, ‖decodeRow L w p u select (x j) - v j‖ ≤ E)
    (hw : (mixGain c : ℝ)*M*2^p < 2^(w u)) (b : Fin o) :
    ‖decodeRow L w p u select (mix L w c u x b) - idealMixRow c v b‖ ≤
      Real.sqrt (Fintype.card J) * ((2:ℝ)/2^p) + mixGain c*E := by
  let z := fun j => decodeRow L w p u select (x j)
  have hs : idealMixRow c z b - idealMixRow c v b = idealMixRow c (fun j => z j-v j) b := by
    simp only [idealMixRow, smul_sub, sum_sub_distrib]
  calc
    _ ≤ _ := norm_sub_le_norm_sub_add_norm_sub _ (idealMixRow c z b) _
    _ ≤ _ := add_le_add (mix_row_round L w c p u select x M hM hx hw b)
      (hs ▸ idealMixRow_gain c _ E hE herr b)

end PhysicalWalshGrid

end NearSquareRoot
end Computability
end OAI
