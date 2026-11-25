import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! A polynomial step bound for the indexed LLL loop when a failing Lovász test
decreases the positive integral determinant potential by a factor at most three quarters. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

/-- The cube improves a three-quarters contraction to a factor strictly below one half. -/
theorem swap_size_cube_lt {P Q : ℕ} (hQ : 0 < Q) (h : 4 * Q ≤ 3 * P) :
    (Q ^ 3).size < (P ^ 3).size := by
  have hpow := Nat.pow_le_pow_left h 3
  have hdouble : 2 * Q ^ 3 ≤ P ^ 3 := by
    simp only [mul_pow] at hpow
    norm_num at hpow
    omega
  have hsize := Nat.size_le_size hdouble
  have hshift := Nat.size_shiftLeft (pow_ne_zero 3 hQ.ne') 1
  have hs : (2 * Q ^ 3).size = (Q ^ 3).size + 1 := by
    simpa [Nat.shiftLeft_eq, Nat.mul_comm] using hshift
  omega

/-- A single integer rank decreases on an advance and on a swap that can move the
cursor back by at most one. -/
def indexedReductionRank (n P k : ℕ) : ℕ := 2 * (P ^ 3).size + (n - k)

theorem indexedReductionRank_advance {n P k : ℕ} (hk : k < n) :
    indexedReductionRank n P (k + 1) < indexedReductionRank n P k := by
  unfold indexedReductionRank
  omega

theorem indexedReductionRank_swap {n P Q k k' : ℕ} (hQ : 0 < Q)
    (h : 4 * Q ≤ 3 * P) (hk : k - 1 ≤ k') :
    indexedReductionRank n Q k' < indexedReductionRank n P k := by
  have := swap_size_cube_lt hQ h
  unfold indexedReductionRank
  omega

/-- Every finite trace of the two actual cursor updates has polynomial length in the
initial potential's binary length and the row count. -/
theorem indexedReduction_length {n T L : ℕ} (P k : ℕ → ℕ) (hinit : P 0 ≤ 2 ^ L)
    (hstep : ∀ t < T,
      (k t < n ∧ P (t+1) = P t ∧ k (t+1) = k t + 1) ∨
      (0 < P (t+1) ∧ 4 * P (t+1) ≤ 3 * P t ∧ k t - 1 ≤ k (t+1))) :
    T ≤ 2 * (3 * L + 1) + n := by
  let rank t := indexedReductionRank n (P t) (k t)
  have hdec (t : ℕ) (ht : t < T) : rank (t + 1) < rank t := by
    obtain ⟨hk, hp, hk'⟩ | ⟨hp, hr, hk'⟩ := hstep t ht
    · simpa [rank, hp, hk'] using indexedReductionRank_advance (P := P t) hk
    · exact indexedReductionRank_swap hp hr hk'
  have htel (t : ℕ) (ht : t ≤ T) : t + rank t ≤ rank 0 := by
    induction t with
    | zero => simp
    | succ t ih =>
      have h := hdec t (by omega)
      have h' := ih (by omega)
      omega
  have hcube : (P 0) ^ 3 ≤ 2 ^ (3 * L) := by
    calc
      _ ≤ (2 ^ L) ^ 3 := Nat.pow_le_pow_left hinit 3
      _ = _ := by rw [← pow_mul, Nat.mul_comm L 3]
  have hs := Nat.size_le_size hcube
  rw [Nat.size_pow] at hs
  have htot := htel T le_rfl
  dsimp [rank, indexedReductionRank] at htot
  omega

end Lattice
end LinearProgramming
end Optimization
end OAI
