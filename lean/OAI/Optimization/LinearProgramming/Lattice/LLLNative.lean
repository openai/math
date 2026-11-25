import OAI.Optimization.LinearProgramming.Lattice.LLLReduction
import OAI.Optimization.LinearProgramming.Lattice.LLLIndependence
import HexMatrixMathlib.Gram
import HexGramSchmidtMathlib.Basic
import HexLLLMathlib.ShortVector

/-! This module uses the Hex matrix and Gram–Schmidt libraries to transfer the native
integer LLL reducer and its guarantees to rational matrices. The imported Hex modules,
including the [short-vector proof](https://github.com/leanprover/hex-lll-theory/blob/761108380d7bdae23181785d52703b4883388da1/HexLLLMathlib/ShortVector.lean),
are by Kim Morrison (© 2026 Lean FRO, LLC, Apache-2.0). -/

open Finset InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

/-- The native rational coefficient is precisely the real Gram–Schmidt coefficient. -/
theorem nativeCoeff_eq {n m : ℕ} (b : Hex.Matrix ℤ (n + 1) m)
    {i j : Fin (n + 1)} (hj : j < i) :
    (((Hex.GramSchmidt.Int.coeffs b)[i][j] : ℚ) : ℝ) =
      gsCoeff (Hex.GramSchmidtMathlib.intRowFamily b) i j := by
  have h := Hex.GramSchmidtMathlib.rat_coeffs_lower_projection_real
    (Hex.GramSchmidtMathlib.castIntMatrix b) hj
  rw [gsCoeff, ← Hex.GramSchmidtMathlib.int_basis_row_eq_gramSchmidt]
  exact h

/-- The native squared length is precisely the Mathlib Euclidean squared norm. -/
theorem nativeNormSq_eq {n m : ℕ} (b : Hex.Matrix ℤ (n + 1) m)
    (j : Fin (n + 1)) :
    ((Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis b) j : ℚ) : ℝ) =
    ‖gramSchmidt ℝ (Hex.GramSchmidtMathlib.intRowFamily b) j‖^2 := by
  rw [← Hex.GramSchmidtMathlib.int_basis_row_eq_gramSchmidt, ← real_inner_self_eq_norm_sq,
      Hex.GramSchmidtMathlib.rowToEuclidean_inner]
  rfl

/-- The exact integer LLL implementation gives a size- and Lovász-reduced Euclidean row family. -/
theorem nativeLLL_reduced {n m : ℕ} (b : Hex.Matrix ℤ (n + 1) m) (h : b.independent) :
    LLLReduced (Hex.GramSchmidtMathlib.intRowFamily (Hex.lllNative b (3 / 4))) := by
  let c := Hex.lllNative b (3 / 4)
  have hh : Hex.isLLLReduced c (3 / 4) (1 / 2) :=
    Hex.lllNative_isLLLReduced b (3 / 4) (by norm_num) (by norm_num) (by omega) h
  refine ⟨?_, ?_⟩
  · intro i j hji
    have hs := hh.1 i.val j.val i.isLt hji
    change (Hex.GramSchmidt.Int.coeffs c)[i][j] * (Hex.GramSchmidt.Int.coeffs c)[i][j] ≤
      (1 / 2 : ℚ) * (1 / 2) at hs
    have hR := (Rat.cast_le (K := ℝ)).mpr hs
    push_cast at hR
    rw [nativeCoeff_eq c hji] at hR
    change |gsCoeff (Hex.GramSchmidtMathlib.intRowFamily c) i j| ≤ _
    exact abs_le_of_sq_le_sq (by nlinarith) (by norm_num)
  · intro i
    have hs := hh.2 i.val (show i.val + 1 < n+1 by omega)
    change (3 / 4 : ℚ) * Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis c) i.castSucc ≤
      Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis c) i.succ +
      (Hex.GramSchmidt.Int.coeffs c)[i.succ][i.castSucc] * (Hex.GramSchmidt.Int.coeffs c)[i.succ][i.castSucc] *
      Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis c) i.castSucc at hs
    have hR := (Rat.cast_le (K := ℝ)).mpr hs
    push_cast at hR
    simpa only [nativeNormSq_eq, nativeCoeff_eq c Fin.castSucc_lt_succ, pow_two] using hR

/-- The row used by Hex Gram–Schmidt is its integer matrix row in Euclidean coordinates. -/
theorem hexRow_real {n m : ℕ} (b : Hex.Matrix ℤ n m) (i : Fin n) :
    Hex.GramSchmidtMathlib.intRowFamily b i = euclideanIntegerRow (HexMatrixMathlib.matrixEquiv b i) := by
  ext j
  simp [Hex.GramSchmidtMathlib.intRowFamily, Hex.GramSchmidtMathlib.ratRowFamily,
    Hex.GramSchmidtMathlib.rowToEuclidean, Hex.GramSchmidtMathlib.castIntMatrix,
    euclideanIntegerRow, Hex.Matrix.row]

private theorem hexLattice_span {n m : ℕ} (b : Hex.Matrix ℤ n m) :
    HexLLLMathlib.latticeSubmodule b = Submodule.span ℤ (Set.range (HexMatrixMathlib.matrixEquiv b)) := by
  unfold HexLLLMathlib.latticeSubmodule
  congr 2
  funext i
  exact (HexMatrixMathlib.matrixEquiv_row b i).symm

/-- Independent integer rows satisfy the native positivity tests on every leading Gram determinant. -/
theorem native_independent_of_rows {p n : ℕ} (b : Hex.Matrix ℤ p n)
    (hB : LinearIndependent ℝ (fun i => euclideanIntegerRow (HexMatrixMathlib.matrixEquiv b i))) :
    b.independent := by
  apply Hex.GramSchmidt.Int.independent_of_det_positive
  intro k hk _
  have hdet := HexMatrixMathlib.det_principalSubmatrix_eq_submatrix_det b.gramMatrix k hk
  rw [HexMatrixMathlib.matrixEquiv_gramMatrix b] at hdet
  exact hdet.symm ▸ leading_gram_det_pos (HexMatrixMathlib.matrixEquiv b) hB k hk

/-- Apply the exact integer-only implementation of LLL with Lovász parameter `3/4`. -/
def reduceInteger {p n : ℕ} (B : Matrix (Fin (p+1)) (Fin n) ℤ) : Matrix (Fin (p+1)) (Fin n) ℤ :=
  HexMatrixMathlib.matrixEquiv (Hex.lllNative (HexMatrixMathlib.matrixEquiv.symm B) (3 / 4))

theorem reduceInteger_spec {p n : ℕ} (B : Matrix (Fin (p+1)) (Fin n) ℤ)
    (hB : LinearIndependent ℝ (fun i => euclideanIntegerRow (B i))) :
    LLLReduced (fun i => euclideanIntegerRow (reduceInteger B i)) ∧
      Submodule.span ℤ (Set.range (reduceInteger B)) = Submodule.span ℤ (Set.range B) := by
  let b := HexMatrixMathlib.matrixEquiv.symm B
  have he : HexMatrixMathlib.matrixEquiv b = B := HexMatrixMathlib.matrixEquiv.apply_symm_apply B
  have hind : b.independent := native_independent_of_rows b (he.symm ▸ hB)
  constructor
  · let c := Hex.lllNative b (3 / 4)
    have hh : LLLReduced (Hex.GramSchmidtMathlib.intRowFamily c) := nativeLLL_reduced b hind
    rw [show Hex.GramSchmidtMathlib.intRowFamily c = _ from funext (hexRow_real c)] at hh
    exact hh
  · let c := Hex.lllNative b (3 / 4)
    have hsp : HexLLLMathlib.latticeSubmodule c = HexLLLMathlib.latticeSubmodule b := by
      ext x
      exact HexLLLMathlib.lllNative_mem_latticeSubmodule_iff b _ (by norm_num) (by norm_num) (by omega) x
    simpa only [hexLattice_span, he, reduceInteger, b, c] using hsp

/-- Appendix A's reduction on rational matrices, with a single common denominator for all entries. -/
def reduceRational {p n : ℕ} (A : Matrix (Fin (p+1)) (Fin n) ℚ) : Matrix (Fin (p+1)) (Fin n) ℚ :=
  reduceRationalWith reduceInteger A

theorem reduceRational_spec {p n : ℕ} (A : Matrix (Fin (p+1)) (Fin n) ℚ)
    (hA : LinearIndependent ℝ (fun i => euclideanRow (A i))) :
    LLLReduced (fun i => euclideanRow (reduceRational A i)) ∧
      Submodule.span ℤ (Set.range (reduceRational A)) = Submodule.span ℤ (Set.range A) :=
  reduceRationalWith_spec reduceInteger reduceInteger_spec A hA

/-- The returned rows form a basis of exactly the original integer row lattice. -/
theorem reduceRational_basis {p n : ℕ} (A : Matrix (Fin (p+1)) (Fin n) ℚ)
    (hA : LinearIndependent ℚ A) :
    LinearIndependent ℚ (reduceRational A) ∧
      Submodule.span ℤ (Set.range (reduceRational A)) = Submodule.span ℤ (Set.range A) := by
  have hind := (euclideanRow_linearIndependent_iff A).mpr hA
  have hspan := (reduceRational_spec A hind).2
  exact ⟨(euclideanRow_linearIndependent_iff _).mp
    (independent_of_same_integer_row_lattice hind hspan), hspan⟩

/-- The algorithmic basis from Appendix A preserves the whole integer row lattice. Each
nonzero rational lattice vector belongs to a prefix with the advertised bound on *all* its rows. -/
theorem reduceRational_short_prefix {p n : ℕ} (A : Matrix (Fin (p+1)) (Fin n) ℚ)
    (hA : LinearIndependent ℚ A) (x : Fin n → ℚ)
    (hx : x ∈ Submodule.span ℤ (Set.range A)) (hx0 : x ≠ 0) :
    ∃ j : Fin (p+1), x ∈ Submodule.span ℤ (reduceRational A '' Set.Iic j) ∧
      ∀ i ≤ j, ‖euclideanRow (reduceRational A i)‖ ≤ (2 : ℝ)^(p+1) * ‖euclideanRow x‖ := by
  obtain ⟨hr, hspan⟩ := reduceRational_spec A ((euclideanRow_linearIndependent_iff A).mpr hA)
  have hx' : x ∈ Submodule.span ℤ (Set.range (fun i => reduceRational A i)) := hspan.symm ▸ hx
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ (v := fun i => reduceRational A i) (x := x)).mp hx'
  have hcomb : euclideanRow x = ∑ i, (a i : ℝ) • euclideanRow (reduceRational A i) :=
    (congrArg euclideanRow ha.symm).trans (euclideanRow_sum a (reduceRational A))
  have hne : euclideanRow x ≠ 0 := by
    intro h0
    apply hx0
    ext j
    have hj := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v j) h0
    change (x j : ℝ) = 0 at hj
    exact_mod_cast hj
  obtain ⟨j, hsupport, hbound⟩ := lll_short_prefix_support hr a hcomb hne
  refine ⟨j, ?_, hbound⟩
  rw [← ha]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i ≤ j
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · simp [hsupport i (lt_of_not_ge hi)]

end Lattice
end LinearProgramming
end Optimization
end OAI
