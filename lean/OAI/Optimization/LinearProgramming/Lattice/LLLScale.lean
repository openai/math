import OAI.Optimization.LinearProgramming.Lattice.LLL
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! Transport between the integer and rational row bases in Appendix A. -/

open Finset InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p n : ℕ}

/-- Gram–Schmidt commutes with uniform nonzero scaling, because every projection line is unchanged. -/
theorem gramSchmidt_scale (b : Fin (p+1) → E) {c : ℝ} (hc : c ≠ 0) (i : Fin (p+1)) :
    gramSchmidt ℝ (fun j => c • b j) i = c • gramSchmidt ℝ b i := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    rw [gramSchmidt_def ℝ (fun j => c • b j) i, gramSchmidt_def ℝ b i, smul_sub, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [ih j (Finset.mem_Iio.mp hj)]
    have he : (ℝ ∙ c • gramSchmidt ℝ b j) = (ℝ ∙ gramSchmidt ℝ b j) :=
      Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc) _
    simp only [he, map_smul]

/-- All off-diagonal Gram–Schmidt coefficients are invariant under a common nonzero scaling. -/
theorem gsCoeff_scale (b : Fin (p+1) → E) {c : ℝ} (hc : c ≠ 0) (i j : Fin (p+1)) :
    gsCoeff (fun k => c • b k) i j = gsCoeff b i j := by
  simp only [gsCoeff, gramSchmidt_scale b hc, real_inner_smul_left, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  by_cases hn : ‖gramSchmidt ℝ b j‖ = 0
  · simp [hn]
  · field_simp

theorem LLLReduced.scale {b : Fin (p+1) → E} (hb : LLLReduced b) {c : ℝ} (hc : c ≠ 0) :
    LLLReduced (fun i => c • b i) := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · simpa only [gsCoeff_scale b hc] using hb.size i j hji
  · simp only [gramSchmidt_scale b hc, gsCoeff_scale b hc, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    nlinarith [mul_le_mul_of_nonneg_left (hb.lovasz i) (sq_nonneg c)]

/-- Rational rows embedded in the standard Euclidean space. -/
def euclideanRow (b : Fin n → ℚ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => (b i : ℝ))

/-- Independence of rational generators is equivalent to independence of their real Euclidean images. -/
theorem euclideanRow_linearIndependent_iff {ι : Type*} (A : ι → Fin n → ℚ) :
    LinearIndependent ℝ (fun i => euclideanRow (A i)) ↔ LinearIndependent ℚ A := by
  let e := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  have he := e.toLinearMap.linearIndependent_iff (LinearMap.ker_eq_bot.mpr e.injective)
    (v := fun i => algebraMap ℚ ℝ ∘ A i)
  exact he.trans linearIndependent_algebraMap_comp_iff

/-- Integer combinations of rational rows commute with the Euclidean embedding. -/
theorem euclideanRow_sum {ι : Type*} [Fintype ι] (a : ι → ℤ) (f : ι → Fin n → ℚ) :
    euclideanRow (∑ i, a i • f i) = ∑ i, (a i : ℝ) • euclideanRow (f i) := by
  apply PiLp.ext
  intro k
  change ((∑ i, a i • f i) k : ℝ) = _
  rw [Finset.sum_apply]
  simp [euclideanRow, zsmul_eq_mul, Pi.smul_apply]

/-- Integer row-lattice equality preserves the real span and hence independence for
families of equal cardinality. -/
theorem independent_of_same_integer_row_lattice {ι : Type*} [Fintype ι]
    {f g : ι → Fin n → ℚ} (hf : LinearIndependent ℝ (fun i => euclideanRow (f i)))
    (hspan : Submodule.span ℤ (Set.range g) = Submodule.span ℤ (Set.range f)) :
    LinearIndependent ℝ (fun i => euclideanRow (g i)) := by
  have contain {r s : ι → Fin n → ℚ} (h : Submodule.span ℤ (Set.range r) ≤ Submodule.span ℤ (Set.range s)) :
      Submodule.span ℝ (Set.range fun i => euclideanRow (r i)) ≤
      Submodule.span ℝ (Set.range fun i => euclideanRow (s i)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hm : r i ∈ Submodule.span ℤ (Set.range s) := h (Submodule.subset_span (Set.mem_range_self i))
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ..).mp hm
    change euclideanRow (r i) ∈ _
    rw [← ha, euclideanRow_sum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  have heq := le_antisymm (contain hspan.le) (contain hspan.ge)
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, heq]
  exact (linearIndependent_iff_card_eq_finrank_span.mp hf)

end Lattice
end LinearProgramming
end Optimization
end OAI
