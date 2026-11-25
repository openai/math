import OAI.Optimization.LinearProgramming.Lattice.OracleRows

/-! Clearing a common denominator before integer lattice reduction (Appendix A). -/

open Finset
open scoped BigOperators

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

theorem denominator_dvd_matrixDenominator {p n : ℕ} (A : Matrix (Fin p) (Fin n) ℚ)
    (i : Fin p) (j : Fin n) : (A i j).den ∣ matrixDenominator A :=
  (Finset.dvd_prod_of_mem (fun k => (A i k).den) (Finset.mem_univ j)).trans
    (Finset.dvd_prod_of_mem (fun l => ∏ k, (A l k).den) (Finset.mem_univ i))

theorem integralRows_spec {p n : ℕ} (A : Matrix (Fin p) (Fin n) ℚ)
    (i : Fin p) (j : Fin n) :
    (integralRows A i j : ℚ) = (matrixDenominator A : ℚ) * A i j := by
  have hdiv := Nat.div_mul_cancel (denominator_dvd_matrixDenominator A i j)
  have hq : (A i j).den ≠ 0 := (A i j).den_nz
  rw [← Rat.num_div_den (A i j)]
  unfold integralRows
  simp only [Int.cast_mul, Int.cast_natCast]
  rw [← mul_div_assoc, eq_div_iff (by exact_mod_cast hq)]
  have h : ((matrixDenominator A / (A i j).den : ℕ) : ℚ) * ((A i j).den : ℚ) =
      matrixDenominator A := by exact_mod_cast hdiv
  calc
    _ = (A i j).num * (((matrixDenominator A / (A i j).den : ℕ) : ℚ) * ((A i j).den : ℚ)) := by ring
    _ = _ := by rw [h, mul_comm]

/-- Scaling acts uniformly on *all* integer combinations in the row lattice. -/
theorem integralRows_combination {p n : ℕ} (A : Matrix (Fin p) (Fin n) ℚ)
    (a : Fin p → ℤ) (j : Fin n) :
    ((∑ i, a i * integralRows A i j : ℤ) : ℚ) =
      (matrixDenominator A : ℚ) * (∑ i, (a i : ℚ) * A i j) := by
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [integralRows_spec]; ring

/-- Product-denominator size bound, with each input denominator less than or equal to `2^L`. -/
theorem matrixDenominator_le {p n L : ℕ} (A : Matrix (Fin p) (Fin n) ℚ)
    (hd : ∀ i j, (A i j).den ≤ 2 ^ L) : matrixDenominator A ≤ 2 ^ (L * n * p) := by
  calc
    matrixDenominator A ≤ ∏ _i : Fin p, ∏ _j : Fin n, 2 ^ L :=
      Finset.prod_le_prod fun i _ => Finset.prod_le_prod fun j _ => hd i j
    _ = _ := by simp [pow_mul]

/-- The scaled integer entries have polynomially many bits in the input dimensions and lengths. -/
theorem integralRows_natAbs_le {p n L : ℕ} (A : Matrix (Fin p) (Fin n) ℚ)
    (hn : ∀ i j, (A i j).num.natAbs ≤ 2 ^ L) (hd : ∀ i j, (A i j).den ≤ 2 ^ L)
    (i : Fin p) (j : Fin n) : (integralRows A i j).natAbs ≤ 2 ^ (L + L * n * p) := by
  unfold integralRows
  rw [pow_add, Int.natAbs_mul]
  rw [Nat.mul_comm (2 ^ L)]
  exact Nat.mul_le_mul ((Nat.div_le_self _ _).trans (matrixDenominator_le A hd)) (hn i j)

end Lattice
end LinearProgramming
end Optimization
end OAI
