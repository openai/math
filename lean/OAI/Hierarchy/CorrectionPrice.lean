import OAI.Hierarchy.CorrectionProducts
import OAI.Hierarchy.SparseCorrection

namespace OAI
/-! # Price discount for the discarded part of a sparse tensor expansion -/

noncomputable section
namespace Hierarchy.CorrectionPrice

open CorrectionProducts
open scoped BigOperators Classical NNReal

variable {I J : Type} [Fintype I] [Fintype J] [Nonempty J] {F : Type*} [Field F]

def omitted {s : ℕ} (p : ℕ) (error ordinary : (I → Bool) → F)
    (x : (Fin s × I) → Bool) : F :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin s) => p < S.card),
    SparseCorrection.term (fun j => error (fun i => x (j,i)))
      (fun j => ordinary (fun i => x (j,i))) S

theorem value_omitted_le (φ : Point J F) (σ : I → J) (s p : ℕ)
    (error ordinary : (I → Bool) → F) {B h z : ℝ}
    (hB : 0 ≤ B) (hh : 0 < h) (hz : 0 ≤ z) (hsmall : h*z ≤ 1)
    (he : (value φ σ error : ℝ) ≤ B*z) (ho : (value φ σ ordinary : ℝ) ≤ B*(1+z)) :
    (value φ (σ ∘ Prod.snd) (omitted (s := s) p error ordinary) : ℝ) ≤
       B^s * ((h*z)^(p+1)*(1+z+1/h)^s) := by
  let A := Finset.univ.filter (fun S : Finset (Fin s) => p < S.card)
  let term (S : Finset (Fin s)) (x : Fin s × I → Bool) :=
    SparseCorrection.term (fun j => error (fun i => x (j,i)))
      (fun j => ordinary (fun i => x (j,i))) S
  have expand : omitted (s := s) p error ordinary = ∑ S ∈ A, term S := by
    funext x
    simp [omitted,A,term,Finset.sum_apply]
  rw [expand]
  have hv := value_finset_sum_le φ (σ ∘ Prod.snd) A term
  apply (show (value φ (σ ∘ Prod.snd) (∑ S ∈ A, term S) : ℝ) ≤
    ∑ S ∈ A, (value φ (σ ∘ Prod.snd) (term S) : ℝ) by exact_mod_cast hv).trans
  calc
    _ ≤ ∑ S ∈ A, B^s*(z^S.card*(1+z)^Sᶜ.card) := by
      apply Finset.sum_le_sum
      intro S _
      rw [show value φ (σ ∘ Prod.snd) (term S) =
          value φ σ error ^ S.card * value φ σ ordinary ^ Sᶜ.card from
          value_mixed φ σ S error ordinary]
      push_cast
      have hn : S.card + Sᶜ.card = s := by simp
      calc
        _ ≤ (B*z)^S.card * (B*(1+z))^Sᶜ.card := by gcongr
        _ = _ := by
          have powers : B^S.card*B^Sᶜ.card=B^s := (pow_add B ..).symm.trans (congrArg (B^·) hn)
          rw [mul_pow,mul_pow,← powers]
          ring
    _ = B^s * ∑ S ∈ A, z^S.card*(1+z)^Sᶜ.card := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (SparseCorrection.omitted_le s p hh hz hsmall)
      (pow_nonneg hB _)

private theorem exponentiated {x c R : ℝ} (hx : 0 < x) (hc : 0 < c)
    (bound : c*Real.logb 2 x ≤ R) : x ≤ (2:ℝ)^(R/c) :=
  (Real.logb_le_iff_le_rpow (by norm_num) hx).mp ((le_div_iff₀ hc).mpr (by linarith))

/-- Price on the genuine normalized spectral point for the whole grouped output.
Only the bounded ideal and the original one-copy error gap are required. -/
theorem discounted (φ : Point J F) (σ : I → J) (s p : ℕ)
    (ideal ordinary : (I → Bool) → F) {R c D h : ℝ}
    (hc : 0 < c) (hh : 1 ≤ h)
    (threshold : 2*c*(Real.logb 2 h+3) ≤ D) (copies : (s:ℝ)/h ≤ p+1)
    (base : ideal ≠ 0 → c*Real.logb 2 (value φ σ ideal) ≤ R)
    (discount : ideal-ordinary ≠ 0 → c*Real.logb 2 (value φ σ (ideal-ordinary)) ≤ R-D)
    (nz : omitted (s := s) p (ideal-ordinary) ordinary ≠ 0) :
    c*Real.logb 2 (value φ (σ ∘ Prod.snd) (omitted (s := s) p (ideal-ordinary) ordinary)) ≤
      (s:ℝ)*R-(s:ℝ)*D/(2*h) := by
  let B := (2:ℝ)^(R/c)
  let z := (2:ℝ)^(-D/c)
  have hB : 0 < B := Real.rpow_pos_of_pos (by norm_num) _
  have hz : 0 < z := Real.rpow_pos_of_pos (by norm_num) _
  have hhpos : 0 < h := one_pos.trans_le hh
  have hlog := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hh
  have hsz : z ≤ 1/h := by
    calc
      z ≤ (2:ℝ)^(-Real.logb 2 h) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        apply (div_le_iff₀ hc).mpr
        nlinarith [mul_nonneg hc.le hlog]
      _ = _ := by rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
                       Real.rpow_logb (by norm_num) (by norm_num) hhpos, one_div]
  have bnd : (value φ σ ideal : ℝ) ≤ B := by
    by_cases null : ideal = 0
    · simpa [null] using hB.le
    · exact exponentiated (by exact_mod_cast value_pos φ σ null) hc (base null)
  have err : (value φ σ (ideal-ordinary) : ℝ) ≤ B*z := by
    by_cases null : ideal-ordinary=0
    · simpa [null] using (mul_nonneg hB.le hz.le)
    · apply (exponentiated (by exact_mod_cast value_pos φ σ null) hc (discount null)).trans_eq
      dsimp [B,z]
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
      congr 1
      ring
  have hOrd : (value φ σ ordinary : ℝ) ≤ B*(1+z) := by
    have h := value_add_le φ σ ideal (-(ideal-ordinary))
    rw [value_neg, show ideal + -(ideal-ordinary) = ordinary by abel] at h
    have h' : (value φ σ ordinary : ℝ) ≤ (value φ σ ideal : ℝ) +
        (value φ σ (ideal-ordinary) : ℝ) := by exact_mod_cast h
    nlinarith
  have upper := value_omitted_le φ σ s p (ideal-ordinary) ordinary hB.le hhpos hz.le
    (by simpa only [mul_comm] using (le_div_iff₀ hhpos).mp hsz) err hOrd
  have exactLog (u : ℝ) : c * Real.logb 2 ((2:ℝ)^(u/c)) = u := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos (by norm_num), Real.logb_self_eq_one (by norm_num)]
    field_simp
  have disc := SparseCorrection.price_discount hhpos hc hz hsz (exactLog (-D)) threshold copies
  have pos : 0 < (value φ (σ ∘ Prod.snd) (omitted (s := s) p (ideal-ordinary) ordinary) : ℝ) :=
    by exact_mod_cast value_pos φ (σ ∘ Prod.snd) nz
  have up := mul_le_mul_of_nonneg_left (Real.logb_le_logb_of_le
    (by norm_num : (1:ℝ)<2) pos upper) hc.le
  rw [Real.logb_mul (pow_pos hB _).ne' (by positivity), Real.logb_pow] at up
  nlinarith [show (s:ℝ)*(c*Real.logb 2 B) = s*R by rw [exactLog]]

end Hierarchy.CorrectionPrice

end
end OAI
