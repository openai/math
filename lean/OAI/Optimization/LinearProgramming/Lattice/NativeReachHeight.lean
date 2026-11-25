import OAI.Optimization.LinearProgramming.Lattice.LLLRowOrigin
import OAI.Optimization.LinearProgramming.Lattice.NativeRowHeight

/-! Bounds for the basis entries at all reachable native LLL cursors. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open Hex.Internal Hex.GramSchmidtMathlib

private theorem intFamily_row_congr {n m : ℕ} {A B : Hex.Matrix ℤ n m} {i j : Fin n}
    (h : A.row i = B.row j) : intRowFamily A i = intRowFamily B j := by
  rw [hexRow_real, hexRow_real]
  congr 1
  ext l
  have hh := congrArg (fun row : Vector ℤ m => row[l]) h
  simpa only [Hex.Matrix.getElem_row, HexMatrixMathlib.matrixEquiv_apply] using hh

/-- Every Euclidean row norm is bounded using the starting rows and the largest
possible norm of the row produced by a completed size-reduction pass. -/
theorem nativeReach_row_norm {n m : ℕ} {c d : ReductionCursor (n+1) m} (h : c.Reaches d)
    (hv : c.state.Valid) (hi : c.state.b.independent) {C : ℝ}
    (hC : ∀ i, ‖intRowFamily c.state.b i‖ ≤ C) (i : Fin (n+1)) :
    ‖intRowFamily d.state.b i‖ ≤ max C ((n+1 : ℕ) * (fullGramProduct c.state : ℝ)) := by
  obtain ⟨j,hj⟩ | ⟨a,hca,_,hk,he⟩ := nativeReach_row_origin h i
  · rw [intFamily_row_congr hj]
    exact (hC j).trans (le_max_left ..)
  · rw [intFamily_row_congr he]
    obtain ⟨ha,hI,_⟩ := nativeReach_invariants hca hv hi
    exact (native_sizeReduce_row_height a.state ha hI
      (fun j => (nativeReach_gramSlot_le hca hv hi j).2) ⟨a.index,hk⟩).trans (le_max_right ..)

private theorem input_norm_bound {n m L : ℕ} (b : Hex.Matrix ℤ n m)
    (hB : ∀ i j, ((HexMatrixMathlib.matrixEquiv b) i j).natAbs ≤ 2^L) (i : Fin n) :
    ‖intRowFamily b i‖ ≤ (((m+1)*2^L : ℕ) : ℝ) := by
  rw [hexRow_real]
  have hh := integerRow_norm_sq_bound (HexMatrixMathlib.matrixEquiv b i) (hB i)
  apply le_of_sq_le_sq _ (by positivity)
  apply hh.trans
  push_cast
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (m : ℝ)]) (by positivity)

/-- Polynomial in the dimensions and the input coefficient length. -/
def nativeRowBitBound (n m L : ℕ) : ℕ := (n+m+2*L)*n*n + n + m + L + 3

/-- All basis entries at every pass boundary have a uniform binary size bound.
Swaps merely permute stored rows, so no accumulation of bounds over passes occurs. -/
theorem nativeReach_basis_entry_size {n m L : ℕ} (b : Hex.Matrix ℤ (n+1) m) (hi : b.independent)
    (hB : ∀ i j, ((HexMatrixMathlib.matrixEquiv b) i j).natAbs ≤ 2^L)
    {d : ReductionCursor (n+1) m} (h : (initialReductionCursor b (by omega)).Reaches d)
    (i : Fin (n+1)) (j : Fin m) :
    ((HexMatrixMathlib.matrixEquiv d.state.b) i j).natAbs.size ≤ nativeRowBitBound (n+1) m L := by
  let t := n+1
  let e := (t+m+2*L)*t*t+1
  have hv := HexLLLMathlib.LLLState.ofBasis_valid b
  have hnorm := nativeReach_row_norm h hv hi (input_norm_bound b hB) i
  change ‖intRowFamily d.state.b i‖ ≤ max (((m+1)*2^L : ℕ) : ℝ)
    ((t : ℝ) * (fullGramProduct (LLLState.ofBasis b) : ℝ)) at hnorm
  have hg : fullGramProduct (LLLState.ofBasis b) ≤ 2^e := by
    rw [initialFullGramProduct_eq b (by omega)]
    exact (Nat.size_le.mp (reductionPotential_size_le _ hB)).le
  have hinput : (m+1)*2^L ≤ 2^(m+1+L) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ (Nat.lt_two_pow_self.le)
  have hwork : t * fullGramProduct (LLLState.ofBasis b) ≤ 2^(t+e) := by
    rw [pow_add]
    exact Nat.mul_le_mul Nat.lt_two_pow_self.le hg
  let bound := nativeRowBitBound t m L - 1
  have h₀ : m+1+L ≤ bound := by dsimp [bound, nativeRowBitBound, t]; omega
  have h₁ : t+e ≤ bound := by dsimp [bound, nativeRowBitBound, e]; omega
  have hbound : max (((m+1)*2^L : ℕ) : ℝ) ((t : ℝ) * (fullGramProduct (LLLState.ofBasis b) : ℝ))
       ≤ (2 : ℝ)^bound := by
    apply max_le
    · exact_mod_cast hinput.trans (Nat.pow_le_pow_right (by decide) h₀)
    · exact_mod_cast hwork.trans (Nat.pow_le_pow_right (by decide) h₁)
  have hcoord := (PiLp.norm_apply_le (intRowFamily d.state.b i) j).trans (hnorm.trans hbound)
  rw [hexRow_real, Real.norm_eq_abs] at hcoord
  change |(((HexMatrixMathlib.matrixEquiv d.state.b) i j : ℤ) : ℝ)| ≤ (2 : ℝ)^bound at hcoord
  have hz : |(HexMatrixMathlib.matrixEquiv d.state.b) i j| ≤ (2 : ℤ)^bound := by exact_mod_cast hcoord
  rw [Int.abs_eq_natAbs] at hz
  have hn : ((HexMatrixMathlib.matrixEquiv d.state.b) i j).natAbs ≤ 2^bound := by exact_mod_cast hz
  have hs := Nat.size_le_size hn
  rw [Nat.size_pow] at hs
  apply hs.trans
  dsimp [bound, nativeRowBitBound, t]
  omega

end Lattice
end LinearProgramming
end Optimization
end OAI
