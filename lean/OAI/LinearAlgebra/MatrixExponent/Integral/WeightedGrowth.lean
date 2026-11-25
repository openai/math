import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.Tag
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.PolynomialDegeneration
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TagPolynomialBranches
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.PermutationPowers
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Weighted

/-!
# The weighted growth bound for actual tensor characters

Use the optimized tag inequality on the determinant and tripling
degenerations for each leg permutation separately.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Integral
open Rectangle
open Upper Upper.TensorClass Upper.TagHeterogeneous

private def poly (f : Character) (m n : ℕ) : ℝ :=
  f (ofTensor (polynomialTensor (m + 1) (n + 1)))

private theorem poly_pos (f : Character) (m n : ℕ) : 0 < poly f m n :=
  f.polynomial_value_pos _ _ (by omega) (by omega)

private theorem root_le {a b p : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (h : a ^ p ≤ b) :
    a ≤ b ^ (1 / p) := by
  have ht := Real.rpow_le_rpow (Real.rpow_nonneg ha p) h (by positivity : 0 ≤ 1 / p)
  rwa [← Real.rpow_mul ha, mul_one_div_cancel hp.ne', Real.rpow_one] at ht

private theorem concave (f : Character) (hp : 0 < f.pX) (m n : ℕ) :
    poly f m (n + 2) ^ (1 / f.pX) + poly f m n ^ (1 / f.pX) ≤
      2 * poly f m (n + 1) ^ (1 / f.pX) := by
  have h := f.shared_tag_optimized_of_pos (by decide : 0 < 2) _
    (determinant_family_value_pos f m n) hp
  rw [ofTensor_determinant_uniform] at h
  have ht := h.trans (f.determinant_graded_le m n)
  simp only [ofTensor_determinant_family, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] at ht
  change (poly f m (n + 2) ^ (1 / f.pX) + poly f m n ^ (1 / f.pX)) ^ f.pX ≤
    (2 : ℝ) ^ f.pX * poly f m (n + 1) at ht
  have h₁ := poly_pos f m n
  have h₂ := poly_pos f m (n + 2)
  have he := root_le hp (by positivity) ht
  rwa [Real.mul_rpow (by positivity) (poly_pos f _ _).le, ← Real.rpow_mul (by norm_num),
    mul_one_div_cancel hp.ne', Real.rpow_one] at he

theorem poly_row (f : Character) (hp : 0 < f.pX) (m : ℕ) :
    Row (fun n => poly f m n ^ (1 / f.pX))
      (fun n => (f (swapYZ (ofTensor (polynomialTensor (m + 1) (n + 1)))) : ℝ) ^ (1 / f.pX)) m := by
  refine ⟨fun n => Real.rpow_pos_of_pos (poly_pos f _ _) _, ?_, ?_⟩
  · apply antitone_nat_of_succ_le
    intro n
    simp only [TensorSpectrum.rowDifference, Nat.add_assoc, Nat.reduceAdd]
    linarith only [concave f hp m n]
  · intro n
    have h := f.shared_tag_optimized_of_pos (by decide : 0 < 3) _
      (tripling_family_value_pos f (m + 1) (n + 1) (by omega) (by omega)) hp
    rw [ofTensor_tripling_uniform] at h
    have ht := h.trans (f.tripling_graded_le (m + 1) (n + 1) (by omega) (by omega))
    simp only [ofTensor_tripling_family, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at ht
    rw [show 3 * (n + 1) + (m + 1) - 1 = (3 * n + m + 2) + 1 by omega] at ht
    have he := root_le hp (by positivity) ht
    unfold poly
    linarith only [he]

private def price (f : Character) (i : Fin 6) (m n : ℕ) : ℝ :=
  Real.log (poly (f.permuted i) m n)

private theorem price_bound (f : Character) (i : Fin 6) : LogBound (price f i) := by
  intro m n
  apply Real.log_le_log (poly_pos _ _ _)
  have h := (f.permuted i).polynomial_value_le (m + 1) (n + 1) (by omega) (by omega)
  push_cast at h
  unfold poly
  linarith

private theorem price_swap (f : Character) (i : Fin 6) :
    Function.swap (price f i) = price f (permuteSwapXY i) := by
  funext m n
  unfold Function.swap price poly
  rw [← swapXY_polynomialTensor (m + 1) (n + 1), f.permuted_swapXY]

private theorem paired_prices (f : Character) (i j : Fin 6) {d : ℝ}
    (hd : 0 < d) (hi : (f.permuted i).pX = d) (hj : (f.permuted j).pX = d)
    (hij : permuteSwapYZ i = j) (hji : permuteSwapYZ j = i) :
    Increments (price f i) (price f j) d := by
  apply increments_of_rows hd (poly_pos _) (poly_pos _)
  · intro m
    have h := poly_row (f.permuted i) (hi.symm ▸ hd) m
    simp only [hi, f.permuted_swapYZ, hij] at h
    exact h
  · intro m
    have h := poly_row (f.permuted j) (hj.symm ▸ hd) m
    simp only [hj, f.permuted_swapYZ, hji] at h
    exact h

theorem character_bound (f : Character) (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    4 * (f.pX * B * C + f.pY * A * C + f.pZ * A * B) ≤ ((A : ℝ) + B + C) ^ 2 := by
  have h (x : ℝ) (hx : x ≤ 1) (i j : ℕ) : x * i * j ≤ (i : ℝ) * j :=
    mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (by positivity) hx) (by positivity)
  have h₁ := h _ f.pX_le_one B C
  have h₂ := h _ f.pY_le_one A C
  have h₃ := h _ f.pZ_le_one A B
  rcases eq_or_lt_of_le f.pX_nonneg with hx | hx
  · rw [← hx]
    linarith only [h₂, h₃, sq_nonneg ((A : ℝ) - B - C)]
  rcases eq_or_lt_of_le f.pY_nonneg with hy | hy
  · rw [← hy]
    linarith only [h₁, h₃, sq_nonneg ((B : ℝ) - A - C)]
  rcases eq_or_lt_of_le f.pZ_nonneg with hz | hz
  · rw [← hz]
    linarith only [h₁, h₂, sq_nonneg ((C : ℝ) - A - B)]
  refine weighted_growth hx.le hy.le hz.le ?_ ?_ ?_
    (price_bound f 0) (price_bound f 2) (price_bound f 3) hA hB hC
  · exact paired_prices f 0 2 hx (by rw [f.permuted_pX]; rfl) (by rw [f.permuted_pX]; rfl)
      rfl rfl
  · rw [price_swap]
    exact paired_prices f 1 3 hy (by rw [f.permuted_pX]; rfl) (by rw [f.permuted_pX]; rfl)
      rfl rfl
  · rw [price_swap, price_swap]
    exact paired_prices f 4 5 hz (by rw [f.permuted_pX]; rfl) (by rw [f.permuted_pX]; rfl)
      rfl rfl

end OAI.LinearAlgebra.MatrixExponent.Integral
