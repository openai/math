import OAI.Optimization.LinearProgramming.Lattice.LLLNative
import OAI.Optimization.LinearProgramming.Lattice.LLLIndependence
import Mathlib.Data.Nat.Size

/-! The integer scaled Gram coefficients read by native size reduction are mixed Gram minors.
Their sizes therefore follow from the current row sizes, independently of earlier updates. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open Finset Matrix

private theorem native_row_dot_le {n m L : ℕ} (b : Hex.Matrix ℤ n m)
    (hb : ∀ (i : Fin n) (j : Fin m), |b[i][j]| ≤ (2 : ℤ) ^ L) (i j : Fin n) :
    |(b.row i).dotProduct (b.row j)| ≤ (m : ℤ) * ((2 : ℤ)^L)^2 := by
  rw [HexMatrixMathlib.dotProduct_eq, dotProduct]
  calc
    _ ≤ ∑ k, |HexMatrixMathlib.vectorEquiv (b.row i) k * HexMatrixMathlib.vectorEquiv (b.row j) k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin m, ((2 : ℤ)^L)^2 := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, pow_two]
      exact mul_le_mul (hb i k) (hb j k) (abs_nonneg _) (by positivity)
    _ = _ := by simp

/-- Every stored below-diagonal coefficient in a valid native state is a determinant of
bounded row dot products. This bounds the exact `ν` entries read by the reduction test. -/
theorem native_scaled_coefficient_bits {n m L : ℕ} (s : Hex.Internal.LLLState n m)
    (hs : s.Valid) (hb : ∀ (i : Fin n) (j : Fin m), |s.b[i][j]| ≤ (2 : ℤ)^L)
    (i j : Fin n) (hji : j < i) :
    ((s.ν.getRow i).get j).natAbs.size ≤ (n+m+2*L)*n+1 := by
  let g := Hex.GramSchmidt.scaledCoeffMatrix s.b i j hji
  let G := HexMatrixMathlib.matrixEquiv g
  let k := j.val + 1
  have hk : k ≤ n := j.isLt
  have hentry (a c : Fin k) : |G a c| ≤ (m : ℤ) * ((2 : ℤ)^L)^2 := by
    rw [show G a c = g[a][c] from HexMatrixMathlib.matrixEquiv_apply ..]
    simp only [g, Hex.GramSchmidt.scaledCoeffMatrix, Hex.Matrix.getElem_ofFn]
    split <;> apply native_row_dot_le _ hb
  have he : (s.ν.getRow i).get j = G.det := by
    calc
      _ = ((Hex.GramSchmidt.Int.scaledCoeffs s.b).getRow i).get j :=
        hs.ν_eq i.val j.val i.isLt j.isLt hji
      _ = Hex.Matrix.det g := by
        exact_mod_cast Hex.GramSchmidt.Int.scaledCoeffs_lower_eq_det_scaledCoeffMatrix s.b i j hji
      _ = _ := HexMatrixMathlib.det_eq _
  have hdet := abs_det_le_factorial_pow G hentry
  have had : G.det.natAbs ≤ k.factorial * (m * (2^L)^2)^k := by
    rw [Int.abs_eq_natAbs] at hdet
    exact_mod_cast hdet
  have hn : k ≤ 2^n := hk.trans Nat.lt_two_pow_self.le
  have hm : m ≤ 2^m := Nat.lt_two_pow_self.le
  have hp : G.det.natAbs ≤ 2 ^ ((n+m+2*L)*n) := calc
    _ ≤ k.factorial * (m*(2^L)^2)^k := had
    _ ≤ (2^n)^k * (2^m*((2^L)^2))^k :=
      Nat.mul_le_mul (k.factorial_le_pow.trans (Nat.pow_le_pow_left hn k))
        (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hm) k)
    _ = 2 ^ ((n+m+2*L)*k) := by
      rw [← mul_pow, ← pow_mul, ← pow_add, ← pow_add, ← pow_mul]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hk)
  rw [he]
  simpa only [Nat.size_pow] using Nat.size_le_size hp

end Lattice
end LinearProgramming
end Optimization
end OAI
