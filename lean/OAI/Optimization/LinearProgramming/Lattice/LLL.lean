import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The norm and span guarantees for an LLL-reduced basis (Appendix A). -/

open Finset InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- The coefficient of the `j`th orthogonal direction in row `i`. -/
noncomputable def gsCoeff (b : Fin (p + 1) → E) (i j : Fin (p + 1)) : ℝ :=
  ⟪gramSchmidt ℝ b j, b i⟫_ℝ / ‖gramSchmidt ℝ b j‖ ^ 2

/-- Size reduction and the Lovász test with parameter `3/4`. -/
structure LLLReduced (b : Fin (p + 1) → E) : Prop where
  size : ∀ i j, j < i → |gsCoeff b i j| ≤ 1 / 2
  lovasz : ∀ i : Fin p,
    (3 / 4 : ℝ) * ‖gramSchmidt ℝ b i.castSucc‖ ^ 2 ≤
      ‖gramSchmidt ℝ b i.succ‖ ^ 2 + gsCoeff b i.succ i.castSucc ^ 2 *
        ‖gramSchmidt ℝ b i.castSucc‖ ^ 2

private theorem gs_adjacent {b : Fin (p + 1) → E} (h : LLLReduced b) (i : Fin p) :
    ‖gramSchmidt ℝ b i.castSucc‖ ≤ 2 * ‖gramSchmidt ℝ b i.succ‖ := by
  have hμ := abs_le.mp (h.size i.succ i.castSucc Fin.castSucc_lt_succ)
  have hμ2 : gsCoeff b i.succ i.castSucc ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hμ.2) (sub_nonneg.mpr hμ.1)]
  have hsq := mul_le_mul_of_nonneg_right hμ2 (sq_nonneg ‖gramSchmidt ℝ b i.castSucc‖)
  have hc := h.lovasz i
  nlinarith [norm_nonneg (gramSchmidt ℝ b i.castSucc), norm_nonneg (gramSchmidt ℝ b i.succ),
    sq_nonneg ‖gramSchmidt ℝ b i.succ‖]

private theorem gs_weight_mono {b : Fin (p + 1) → E} (h : LLLReduced b) :
    Monotone (fun i : Fin (p + 1) => (2 : ℝ) ^ i.val * ‖gramSchmidt ℝ b i‖) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  simp only [Fin.val_castSucc, Fin.val_succ, pow_succ]
  calc
    (2 : ℝ)^i.val * _ ≤ 2^i.val * (2 * _) :=
      mul_le_mul_of_nonneg_left (gs_adjacent h i) (by positivity)
    _ = _ := by ring

private theorem gs_prefix_bound {b : Fin (p + 1) → E} (h : LLLReduced b)
    (i : Fin (p + 1)) :
    ‖gramSchmidt ℝ b i‖ + (∑ j ∈ Iio i, ‖gramSchmidt ℝ b j‖) / 2 ≤
      (2 : ℝ)^i.val * ‖gramSchmidt ℝ b i‖ := by
  induction i using Fin.induction with
  | zero =>
    have h0 : Iio (0 : Fin (p + 1)) = ∅ := by ext k; simp
    simp [h0]
  | succ i ih =>
    have hI : Iio i.succ = insert i.castSucc (Iio i.castSucc) := by
      ext j
      simp only [mem_Iio, mem_insert, Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
      omega
    rw [hI, sum_insert (by simp), Fin.val_succ, pow_succ]
    have hq : 0 ≤ (2 : ℝ) ^ i.val - 1 / 2 := by
      have hp : (1 : ℝ) ≤ 2 ^ i.val := one_le_pow₀ (by norm_num)
      linarith
    have ht := mul_le_mul_of_nonneg_left (gs_adjacent h i) hq
    simp only [Fin.val_castSucc] at ih
    linarith

/-- Every reduced row is bounded by its own Gram-Schmidt length times `2^i`. -/
theorem lll_row_norm_le {b : Fin (p + 1) → E} (h : LLLReduced b) (i : Fin (p + 1)) :
    ‖b i‖ ≤ (2 : ℝ) ^ i.val * ‖gramSchmidt ℝ b i‖ := by
  have hd := gramSchmidt_def'' ℝ b i
  change b i = gramSchmidt ℝ b i + ∑ j ∈ Iio i, gsCoeff b i j • gramSchmidt ℝ b j at hd
  have ht : ‖b i‖ ≤ ‖gramSchmidt ℝ b i‖ + ∑ j ∈ Iio i, ‖gsCoeff b i j • gramSchmidt ℝ b j‖ :=
    calc
      ‖b i‖ = ‖gramSchmidt ℝ b i + ∑ j ∈ Iio i, gsCoeff b i j • gramSchmidt ℝ b j‖ := congrArg norm hd
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
  refine ht.trans (le_trans (add_le_add_right ?_ _) (gs_prefix_bound h i))
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro j hj
  rw [norm_smul, Real.norm_eq_abs, div_eq_mul_inv]
  simpa [mul_comm] using mul_le_mul_of_nonneg_right (h.size i j (mem_Iio.mp hj))
    (norm_nonneg (gramSchmidt ℝ b j))

private theorem gs_inner_row (b : Fin (p + 1) → E) (j : Fin (p + 1)) :
    ⟪gramSchmidt ℝ b j, b j⟫_ℝ = ‖gramSchmidt ℝ b j‖ ^ 2 := by
  calc
    ⟪gramSchmidt ℝ b j, b j⟫_ℝ =
        ⟪gramSchmidt ℝ b j, gramSchmidt ℝ b j + ∑ k ∈ Iio j,
          gsCoeff b j k • gramSchmidt ℝ b k⟫_ℝ :=
      congrArg (inner ℝ (gramSchmidt ℝ b j)) (gramSchmidt_def'' ℝ b j)
    _ = _ := by
      rw [inner_add_right, inner_sum, real_inner_self_eq_norm_sq]
      refine add_eq_left.mpr (Finset.sum_eq_zero fun k hk => ?_)
      rw [real_inner_smul_right, gramSchmidt_orthogonal ℝ b (mem_Iio.mp hk).ne', mul_zero]

/-- All rows up through the last nonzero coefficient satisfy the short-vector bound. -/
theorem lll_short_prefix_support {b : Fin (p + 1) → E}
    (hr : LLLReduced b) (a : Fin (p + 1) → ℤ) {x : E}
    (hx : x = ∑ i, (a i : ℝ) • b i) (hx0 : x ≠ 0) :
    ∃ j : Fin (p + 1), (∀ i, j < i → a i = 0) ∧
      ∀ i ≤ j, ‖b i‖ ≤ (2 : ℝ) ^ (p + 1) * ‖x‖ := by
  classical
  let s := univ.filter fun i => a i ≠ 0
  have hs : s.Nonempty := by
    by_contra! he
    apply hx0
    rw [hx]
    apply Finset.sum_eq_zero
    intro i _
    have hni : i ∉ s := by simp [he]
    have hai : a i = 0 := by simpa [s] using hni
    simp [hai]
  let j := s.max' hs
  have hj : a j ≠ 0 := by simpa [s] using s.max'_mem hs
  have ha (i) (hi : j < i) : a i = 0 := by
    by_contra hn
    have : i ≤ j := s.le_max' i (by simpa [s] using hn)
    exact (not_le_of_gt hi) this
  refine ⟨j, ha, ?_⟩
  have hinner : ⟪gramSchmidt ℝ b j, x⟫_ℝ = (a j : ℝ) * ‖gramSchmidt ℝ b j‖^2 := by
    rw [hx, inner_sum, Finset.sum_eq_single j]
    · rw [real_inner_smul_right, gs_inner_row]
    · intro i _ hij
      rcases lt_or_gt_of_ne hij with hi | hi
      · rw [real_inner_smul_right, gramSchmidt_inv_triangular ℝ b hi, mul_zero]
      · simp [ha i hi]
    · simp
  have habs : (1 : ℝ) ≤ |(a j : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast (Int.one_le_abs hj)
  have hcs := abs_real_inner_le_norm (gramSchmidt ℝ b j) x
  rw [hinner, abs_mul, abs_of_nonneg (sq_nonneg ‖gramSchmidt ℝ b j‖)] at hcs
  have hnorm : ‖gramSchmidt ℝ b j‖ ≤ ‖x‖ := by
    rcases (norm_nonneg (gramSchmidt ℝ b j)).eq_or_lt with hg | hg
    · rw [← hg]
      exact norm_nonneg _
    · have hbnd := mul_le_mul_of_nonneg_right habs (sq_nonneg ‖gramSchmidt ℝ b j‖)
      nlinarith
  intro i hi
  exact (lll_row_norm_le hr i).trans ((gs_weight_mono hr hi).trans
    (mul_le_mul (pow_le_pow_right₀ (by norm_num) j.isLt.le) hnorm
      (norm_nonneg _) (by positivity)))


/-- The prefix guarantee for every nonzero vector in the integer row lattice. -/
theorem lll_short_prefix_of_coefficients {b : Fin (p + 1) → E}
    (hr : LLLReduced b) (a : Fin (p + 1) → ℤ) {x : E}
    (hx : x = ∑ i, (a i : ℝ) • b i) (hx0 : x ≠ 0) :
    ∃ j : Fin (p + 1), x ∈ Submodule.span ℝ (b '' Set.Iic j) ∧
      ∀ i ≤ j, ‖b i‖ ≤ (2 : ℝ) ^ (p + 1) * ‖x‖ := by
  obtain ⟨j, ha, hbound⟩ := lll_short_prefix_support hr a hx hx0
  refine ⟨j, ?_, hbound⟩
  rw [hx]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i ≤ j
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · simp [ha i (lt_of_not_ge hi)]

/-- The short-prefix bound for an independent reduced basis. -/
theorem lll_short_prefix {b : Fin (p + 1) → E} (_hb : LinearIndependent ℝ b)
    (hr : LLLReduced b) (a : Fin (p + 1) → ℤ) {x : E}
    (hx : x = ∑ i, (a i : ℝ) • b i) (hx0 : x ≠ 0) :
    ∃ j : Fin (p + 1), x ∈ Submodule.span ℝ (b '' Set.Iic j) ∧
      ∀ i ≤ j, ‖b i‖ ≤ (2 : ℝ) ^ (p + 1) * ‖x‖ :=
  lll_short_prefix_of_coefficients hr a hx hx0

end Lattice
end LinearProgramming
end Optimization
end OAI
