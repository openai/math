import OAI.LinearAlgebra.SpectralBooks.Fermion.WickNormalMatrix
import OAI.LinearAlgebra.SpectralBooks.Fermion.FermionFactor

/-! # Extracting a pair of homogeneous field modes at a fixed energy -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace Fermion

open LaurentPolynomial

/-- If one Laurent variable is specialized to one, the missing exponent can
still be recovered from the total coupled degree of the two homogeneous modes. -/
private lemma coeff_pair (f g : ℤ → ℤ) (d e B w : ℤ)
    (hf : ∀ b, f b ≠ 0 → d = b) (hg : ∀ b, g b ≠ 0 → e = b)
    (hs : f d ≠ 0 → g e ≠ 0 → d + e = B) :
    (C (f d) * (C (g e) * T e) : LaurentPolynomial ℤ).coeff w =
      f (B-w) * g w := by
  rw [← mul_assoc, ← map_mul, ← single_eq_C_mul_T]
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases he : e = w
  · subst w
    rw [ite_eq_left rfl]
    by_cases hg0 : g e = 0
    · simp [hg0]
    by_cases hd : d = B-e
    · rw [hd]
    have hfd : f d = 0 := by
      by_contra hn
      have := hs hn hg0
      omega
    have hfb : f (B-e) = 0 := by
      by_contra hn
      exact hd (hf _ hn)
    simp [hfd, hfb]
  · rw [ite_eq_right he]
    have hgw : g w = 0 := by
      by_contra hn
      exact he (hg _ hn)
    simp [hgw]

/-- One block uses the constant field, the other uses the Laurent variable.
In either multiplication order, equal total energy shift fixes the other
exponent once the Laurent degree is prescribed. -/
theorem coeff_field_pair {N : ℕ} (i j : State) (α β γ δ : FockState N) (L : ℕ) (w : ℤ)
    (hw : (weight α.val : ℤ) - weight β.val + (weight γ.val - weight δ.val) = 0)
    (hL : 2*(L : ℤ)+2 = (weight i : ℤ)+weight j) :
    (fieldMatrix N false i α β * fieldMatrix N true j γ δ).coeff w =
      blockMode i (-1-L-w) α.val β.val * blockMode j w γ.val δ.val := by
  rw [fieldMatrix_apply, fieldMatrix_apply]
  simp only [fieldExponent, Bool.false_eq_true, ↓reduceIte, T_zero, mul_one]
  let di := modeDegree (i.sort (· ≤ ·)) α.val β.val
  let dj := modeDegree (j.sort (· ≤ ·)) γ.val δ.val
  apply coeff_pair (fun b ↦ blockMode i b α.val β.val) (fun b ↦ blockMode j b γ.val δ.val)
    di dj (-1-L) w
  · exact fun _ hn ↦ modeDegree_of_listMode_ne_zero hn
  · exact fun _ hn ↦ modeDegree_of_listMode_ne_zero hn
  · intro h₁ h₂
    have h₃ := weight_eq_of_blockMode_ne_zero h₁
    have h₄ := weight_eq_of_blockMode_ne_zero h₂
    omega

end Fermion

end

end SpectralBooks
end LinearAlgebra
end OAI
