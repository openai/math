import OAI.Optimization.LinearProgramming.Lattice.NativeRowHeight
import OAI.Optimization.LinearProgramming.Lattice.NativeNearest
import OAI.Optimization.LinearProgramming.Lattice.NativeColumnValidity

/-! Temporary row heights after a single actual native size-reduction column. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open Hex.Internal InnerProductSpace
open scoped RealInnerProductSpace

/-- A coordinate of the native real row family is the actual stored integer. -/
theorem nativeRow_coordinate {n m : ℕ} (b : Hex.Matrix ℤ n m) (i : Fin n) (l : Fin m) :
    Hex.GramSchmidtMathlib.intRowFamily b i l = (b[i][l] : ℝ) := by
  simp [Hex.GramSchmidtMathlib.intRowFamily, Hex.GramSchmidtMathlib.ratRowFamily,
    Hex.GramSchmidtMathlib.rowToEuclidean, Hex.GramSchmidtMathlib.castIntMatrix, Hex.Matrix.row]

/-- Other rows are unchanged by an individual native column operation. -/
theorem native_column_other_row {n m : ℕ} (s : LLLState n m)
    (j k i : Fin n) (hj : j < k) (hi : i ≠ k) :
    Hex.GramSchmidtMathlib.intRowFamily (s.sizeReduceColumn j k hj).b i =
      Hex.GramSchmidtMathlib.intRowFamily s.b i := by
  ext l
  rw [nativeRow_coordinate, nativeRow_coordinate]
  rw [native_column_basis]
  split
  · simp only [Hex.GramSchmidt.Int.sizeReduce, Hex.Matrix.getElem_rowAdd, ite_eq_right hi]
  · rfl

private theorem nativeRow_sizeReduce {n m : ℕ} (b : Hex.Matrix ℤ n m) (j k : Fin n) (r : ℤ) :
    Hex.GramSchmidtMathlib.intRowFamily (Hex.GramSchmidt.Int.sizeReduce b j k r) k =
      Hex.GramSchmidtMathlib.intRowFamily b k - (r : ℝ) • Hex.GramSchmidtMathlib.intRowFamily b j := by
  ext l
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, nativeRow_coordinate,
    Hex.GramSchmidt.Int.sizeReduce, Hex.Matrix.getElem_rowAdd]
  push_cast
  ring

/-- Including skipped and tied columns, one actual update incurs at most the
multiplicative norm factor used for bounding the inner pass. -/
theorem native_column_height {n m K : ℕ} (s : LLLState (n+1) m) (hs : s.Valid)
    (hind : s.b.independent) (hD : ∀ i, s.d.get i ≤ K) {j k : Fin (n+1)} (hjk : j < k)
    {B : ℝ} (hb : ‖Hex.GramSchmidtMathlib.intRowFamily s.b j‖ ≤ B) :
    ‖Hex.GramSchmidtMathlib.intRowFamily (s.sizeReduceColumn j k hjk).b k‖ + 1 ≤
      (1 + ((K : ℝ)+1)*B) * (‖Hex.GramSchmidtMathlib.intRowFamily s.b k‖ + 1) := by
  let a := (s.ν.getRow k).get j
  let d := s.d.get j.succ
  let r := LLLState.nearestQuotient a d
  let f := Hex.GramSchmidtMathlib.intRowFamily s.b
  have hd : 0 < d := native_gram_slot_positive s hs hind _
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have hquot : (a : ℝ) / (d : ℝ) = gsCoeff f k j := by
    apply (div_eq_iff hd'.ne').mpr
    simpa only [mul_comm] using native_stored_coefficient s hs hjk
  have herr : |gsCoeff f k j - (r : ℝ)| ≤ 1/2 := hquot ▸ native_nearest_error a d hd
  have hnear := nearbyIntegerCoefficient_bound (f k) (gramSchmidt ℝ f j) r
    (Nat.cast_nonneg K) (native_gram_length_bounds s hs hind hD j).2 herr
  rw [native_column_basis]
  split
  · change ‖Hex.GramSchmidtMathlib.intRowFamily (Hex.GramSchmidt.Int.sizeReduce s.b j k r) k‖ + 1 ≤ _
    rw [nativeRow_sizeReduce]
    exact sub_integer_row_growth _ _ r (Nat.cast_nonneg K) hb hnear
  · have hB : 0 ≤ B := (norm_nonneg _).trans hb
    apply le_mul_of_one_le_left (by positivity)
    nlinarith [mul_nonneg (show 0 ≤ (K : ℝ) + 1 by positivity) hB]

end Lattice
end LinearProgramming
end Optimization
end OAI
