import OAI.LinearAlgebra.SpectralBooks.Fermion.FermionLaurent
import OAI.LinearAlgebra.SpectralBooks.Fermion.FermionProduct
import OAI.LinearAlgebra.SpectralBooks.Fermion.FermionBalanced
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickMultiplier

/-! # Extracting the two shifted integer matrix products -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace Fermion

open Finset Filter LaurentPolynomial

private theorem coeff_sign_mul (n : ℕ) (p : LaurentPolynomial ℤ) (w : ℤ) :
    (((-1 : LaurentPolynomial ℤ)^n) * p).coeff w = ((-1 : ℤ)^n) * p.coeff w := by
  rw [show (-1 : LaurentPolynomial ℤ)^n = C ((-1 : ℤ)^n) by simp,
    ← single_eq_C, AddMonoidAlgebra.coeff_single_mul_apply]
  simp

private theorem coeff_supercomm {N : ℕ} (i j : State) (hi : i.Nonempty)
    (hij : i.card = j.card) (α β : FockState N) (hαβ : weight α.val = weight β.val)
    (s : ℤ) :
    (((1 - T 1) ^ order (weight i) (weight j)) *
        ((fieldMatrix N false i * fieldMatrix N true j) α β -
          (-1 : LaurentPolynomial ℤ)^(i.card*j.card) *
            ((fieldMatrix N true j * fieldMatrix N false i) α β))).coeff s =
      truncatedRhs i j α.val β.val s N := by
  rw [coeff_clear_pow_multiplier]
  apply sum_congr rfl
  intro a _
  congr 1
  simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_sign_mul, Matrix.mul_apply,
    AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  let L := order (weight i) (weight j)
  have hL := two_mul_order_add hi hij
  have hb : -1-(L : ℤ)-(s-a) = -s-1-L+a := by ring
  congr 1
  · trans ∑ k : FockState N, blockMode i (-s-1-L+a) α.val k.val *
      blockMode j (s-a) k.val β.val
    · apply sum_congr rfl
      intro k _
      rw [coeff_field_pair i j α k k β L (s-a) (by omega) hL, hb]
    · exact sum_coe_sort (range N).powerset (fun k ↦
        blockMode i (-s-1-L+a) α.val k * blockMode j (s-a) k β.val)
  · congr 1
    trans ∑ k : FockState N, blockMode j (s-a) α.val k.val *
      blockMode i (-s-1-L+a) k.val β.val
    · apply sum_congr rfl
      intro k _
      rw [mul_comm (fieldMatrix N true j α k),
        coeff_field_pair i j k β α k L (s-a) (by omega) hL, hb, mul_comm]
    · exact sum_coe_sort (range N).powerset (fun k ↦
        blockMode j (s-a) α.val k * blockMode i (-s-1-L+a) k β.val)

private theorem eventually_fits (a : State) : ∀ᶠ N : ℕ in atTop, a ∈ (range N).powerset := by
  filter_upwards [eventually_ge_atTop (weight a)] with N hN
  exact mem_powerset.mpr fun i hi ↦ mem_range.mpr ((mode_lt_weight hi).trans_le hN)

/-- The Laurent coefficient identity at equal weights implies the literal
two-mode coefficient identity at all weights. Different weights give zero
by homogeneity in each multiplication order. -/
theorem truncatedIdentity_of_laurent (h : LaurentCrossingIdentity) : TruncatedIdentity := by
  intro i j a b hi hij s
  change ∀ᶠ N : ℕ in atTop, pairing i j * (if a = b then 1 else 0) = truncatedRhs i j a b s N
  by_cases hab : weight a = weight b
  · filter_upwards [h i j a b hi hij hab s, eventually_fits a, eventually_fits b] with N hN ha hb
    let α : FockState N := ⟨a,ha⟩
    let β : FockState N := ⟨b,hb⟩
    exact (hN α β rfl rfl).symm.trans (coeff_supercomm i j hi hij α β hab s)
  · exact Eventually.of_forall fun N ↦ by
      rw [truncatedRhs_eq_zero_of_weight_ne hi hij hab]
      simp [show a ≠ b from fun he ↦ hab (congrArg weight he)]

end Fermion

end

end SpectralBooks
end LinearAlgebra
end OAI
