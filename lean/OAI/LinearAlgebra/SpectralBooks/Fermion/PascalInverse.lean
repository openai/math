import OAI.LinearAlgebra.SpectralBooks.Fermion.PascalBinet
import OAI.LinearAlgebra.SpectralBooks.Fermion.PascalTriangular
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Integral unimodularity of the fermion pairing

Vandermonde and Cauchy--Binet identify the unsigned pairing with the Gram
matrix of Pascal minors. Energy truncation removes only zero columns from
each row. Equal-energy blocks of the Pascal matrix are identity matrices.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open Matrix Finset

private noncomputable def pascalMatrix (H : ℕ) : Matrix (Label H) (Label H) ℤ :=
  Matrix.of fun i j ↦ pascalMinor i.val j.val

private theorem det_pascalMatrix (H : ℕ) : (pascalMatrix H).det = 1 := by
  classical
  let w (i : Label H) := weight i.val
  have ht : (pascalMatrix H).transpose.BlockTriangular w := by
    intro i j hj
    change pascalMinor j.val i.val = 0
    by_contra hn
    rcases eq_or_weight_lt_of_pascalMinor_ne_zero hn with he | he
    · simp only [w, he, lt_self_iff_false] at hj
    · exact he.not_gt hj
  have hblock (a : ℕ) : ((pascalMatrix H).transpose.toSquareBlock w a) = 1 := by
    ext i j
    by_cases he : i = j
    · subst j
      rw [Matrix.one_apply_eq]
      exact pascalMinor_self i.val.val
    · rw [Matrix.one_apply_ne he]
      change pascalMinor j.val.val i.val.val = 0
      by_contra hn
      rcases eq_or_weight_lt_of_pascalMinor_ne_zero hn with hval | hlt
      · exact he (Subtype.ext (Subtype.ext hval.symm))
      · exact hlt.ne (i.property.trans j.property.symm)
  rw [← Matrix.det_transpose, ht.det]
  simp [hblock]

private theorem gram_pairing (H : ℕ) :
    (Matrix.of (fun i j : Label H ↦ pairing i.val j.val)) =
      (Matrix.diagonal (fun i : Label H ↦ pairingSign i.val)) *
        (pascalMatrix H * (pascalMatrix H).transpose) := by
  classical
  ext i j
  rw [Matrix.diagonal_mul]
  simp only [Matrix.of_apply, pairing, Matrix.mul_apply,
    Matrix.transpose_apply, pascalMatrix]
  congr 1
  have hset {S : Finset ℕ} (hS : S ∈ (states (H : ℤ)).erase ∅) : S ⊆ range H := by
    intro k hk
    exact mem_range.mpr ((mode_lt_weight hk).trans_le (label_weight_le ⟨S,hS⟩))
  rw [pascal_gram_minor (hset i.property)]
  change _ = ∑ a : Label H, pascalMinor i.val a.val * pascalMinor j.val a.val
  rw [Finset.sum_coe_sort ((states (H : ℤ)).erase ∅) (fun S ↦ pascalMinor i.val S * pascalMinor j.val S)]
  symm
  apply sum_subset (fun S hS ↦ mem_powerset.mpr (hset hS))
  intro S _ hS
  by_cases hn : pascalMinor i.val S = 0
  · simp [hn]
  · apply False.elim (hS _)
    apply mem_erase.mpr
    constructor
    · intro h0
      subst S
      have hc : (∅ : Finset ℕ).card ≠ i.val.card := by
        simpa using (label_nonempty i).card_pos.ne
      exact hn (by rw [pascalMinor, stateMinor, dite_eq_right hc])
    · rw [mem_states, Int.ofNat_le]
      rcases eq_or_weight_lt_of_pascalMinor_ne_zero hn with he | he
      · exact he ▸ label_weight_le i
      · exact he.le.trans (label_weight_le i)

/-- The finite truncated coefficient pairing admits an integral left inverse
for all energy cutoffs, including an empty label set. -/
theorem pairing_left_inverse (H : ℕ) :
    ∃ A : Matrix (Label H) (Label H) ℤ,
      A * (Matrix.of (fun i j : Label H ↦ pairing i.val j.val)) = 1 := by
  classical
  apply IsUnit.exists_left_inv
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [gram_pairing, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    det_pascalMatrix, mul_one, mul_one, Matrix.det_diagonal]
  apply IsUnit.prod_univ_iff.mpr
  exact fun i ↦ IsUnit.pow _ (isUnit_one.neg)

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
