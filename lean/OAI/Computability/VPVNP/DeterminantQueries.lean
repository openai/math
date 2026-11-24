import OAI.Computability.VPVNP.DeterminantQueryBounds
import OAI.Computability.VPVNP.RankQuery

/-!
# Computing matrix rank by querying a weighted determinant

The Appendix D.2 rank algorithm scans bidegrees in the reverse characteristic
polynomial of the weighted Gram matrix. A fixed degree in a Gram entry reads
at most two scalar entries of the original matrix. The Schur coefficient query
then evaluates the entire determinant at a single bidegree. The proofs cover
empty matrices, rank zero, and characteristic two.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery

section WeightedGramQuery

open Polynomial

variable {K : Type*} [CommRing K] {n m : ℕ}

/-- A tagged Gram entry has at most one contributing column in each degree. -/
def weightedGramEntryCoeff (M : Matrix (Fin n) (Fin m) K) (i j : Fin n) (z : ℕ) : K :=
  if h : i.val + 2 ≤ z ∧ z - i.val - 2 < m then
    let k : Fin m := ⟨z - i.val - 2, h.2⟩
    M i k * M j k
  else 0

theorem weightedGramEntryCoeff_eq (M : Matrix (Fin n) (Fin m) K) (i j : Fin n) (z : ℕ) :
    weightedGramEntryCoeff M i j z = ((weightedGram M) i j).coeff z := by
  have hentry : (weightedGram M) i j = ∑ k : Fin m,
      C (M i k * M j k) * X ^ (i.val + k.val + 2) := by
    rw [weightedGram, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    simp only [weightDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply,
      Matrix.transpose_apply, map_mul]
    rw [show i.val + k.val + 2 = (i.val + 1) + (k.val + 1) by omega, pow_add X (i.val + 1) (k.val + 1)]
    ac_rfl
  rw [hentry, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  unfold weightedGramEntryCoeff
  split_ifs with h
  · let k : Fin m := ⟨z - i.val - 2, h.2⟩
    rw [Finset.sum_eq_single k]
    · rw [ite_eq_left (by dsimp [k]; omega)]
    · intro l _ hl
      rw [ite_eq_right]
      intro heq
      apply hl
      apply Fin.ext
      dsimp [k]
      omega
    · simp
  · symm
    apply Finset.sum_eq_zero
    intro k _
    rw [ite_eq_right]
    have := k.isLt
    omega

/-- Scan a consecutive interval and return its maximum score, or zero if empty. -/
def streamMaximum (n : ℕ) (f : Fin n → ℕ) : ℕ :=
  Fin.foldl n (fun best i => max best (f i)) 0

theorem streamMaximum_le_iff (n b : ℕ) (f : Fin n → ℕ) :
    streamMaximum n f ≤ b ↔ ∀ i, f i ≤ b := by
  induction n with
  | zero => simp [streamMaximum]
  | succ n ih =>
    rw [streamMaximum, Fin.foldl_succ_last]
    change max (streamMaximum n fun i => f i.castSucc) (f (Fin.last n)) ≤ b ↔ _
    rw [max_le_iff, ih]
    exact ⟨fun h i => Fin.lastCases h.2 (fun i => h.1 i) i,
      fun h => ⟨fun i => h i.castSucc, h (Fin.last n)⟩⟩

theorem le_streamMaximum {n : ℕ} (f : Fin n → ℕ) (i : Fin n) :
    f i ≤ streamMaximum n f :=
  (streamMaximum_le_iff n _ f).mp le_rfl i

theorem indexWeight_le {q n : ℕ} (I : Set.powersetCard (Fin n) q) :
    indexWeight I ≤ q * n := by
  rw [indexWeight_eq_sum]
  calc
    _ ≤ ∑ _i : Fin q, n := Finset.sum_le_sum fun i _ =>
      Nat.succ_le_of_lt (Set.powersetCard.ofFinEmbEquiv.symm I i).isLt
    _ = q * n := by simp

/-- The inner degree at outer degree `u` is at most `u(n+m)`. -/
theorem rankPolynomial_coeff_natDegree_le {K : Type*} [CommRing K] {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) K) (u : ℕ) :
    ((rankPolynomial M).coeff u).natDegree ≤ u * (n + m) := by
  classical
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro z hz
  have sign : (-1 : K[X]) ^ u = C ((-1 : K) ^ u) := by simp
  rw [rankPolynomial_coeff, sign, coeff_C_mul, finsetSum_coeff]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro i _
  rw [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j _
  rw [← map_pow, mul_comm, coeff_C_mul_X_pow, ite_eq_right]
  have hi := indexWeight_le i
  have hj := indexWeight_le j
  rw [Nat.mul_add] at hz
  omega

/-- Recover rank by scanning scalar bidegree queries. The scans include both
endpoints and keep only the current indices and maximum degree. -/
def scanRank {K : Type*} [Zero K] [DecidableEq K] (n m : ℕ) (q : ℕ → ℕ → K) : ℕ :=
  streamMaximum (n + 1) fun u => streamMaximum ((n + m) * n + 1) fun z =>
    if q u.val z.val = 0 then 0 else u.val

theorem scanRank_correct {K : Type*} [Field K] [DecidableEq K] {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) K) (q : ℕ → ℕ → K)
    (hq : ∀ u z, q u z = ((rankPolynomial M).coeff u).coeff z) :
    scanRank n m q = M.rank := by
  let score (u : Fin (n + 1)) (z : Fin ((n + m) * n + 1)) :=
    if q u.val z.val = 0 then 0 else u.val
  change (streamMaximum (n + 1) fun u => streamMaximum ((n + m) * n + 1) (score u)) = M.rank
  apply le_antisymm
  · apply (streamMaximum_le_iff ..).mpr
    intro u
    apply (streamMaximum_le_iff ..).mpr
    intro z
    dsimp [score]
    split_ifs with hzero
    · exact Nat.zero_le _
    · rw [← rankPolynomial_natDegree M]
      apply le_natDegree_of_ne_zero
      intro hu
      exact hzero (by rw [hq, hu, coeff_zero])
  · by_cases hpoly : rankPolynomial M = 0
    · simp [← rankPolynomial_natDegree M, hpoly]
    have htop : (rankPolynomial M).coeff M.rank ≠ 0 := by
      rw [← rankPolynomial_natDegree M, coeff_natDegree, leadingCoeff_ne_zero]
      exact hpoly
    let u : Fin (n + 1) := ⟨M.rank, Nat.lt_succ_of_le M.rank_le_height⟩
    have bound : ((rankPolynomial M).coeff M.rank).natDegree ≤ (n + m) * n := calc
      _ ≤ M.rank * (n + m) := rankPolynomial_coeff_natDegree_le M M.rank
      _ ≤ n * (n + m) := Nat.mul_le_mul_right _ M.rank_le_height
      _ = _ := Nat.mul_comm _ _
    let z : Fin ((n + m) * n + 1) :=
      ⟨((rankPolynomial M).coeff M.rank).natDegree, Nat.lt_succ_of_le bound⟩
    have hscalar : q u.val z.val ≠ 0 := by
      rw [hq]
      change ((rankPolynomial M).coeff M.rank).coeff ((rankPolynomial M).coeff M.rank).natDegree ≠ 0
      rwa [coeff_natDegree, leadingCoeff_ne_zero]
    calc
      M.rank = score u z := by simp [score, hscalar, u]
      _ ≤ streamMaximum _ (score u) := le_streamMaximum _ z
      _ ≤ streamMaximum _ _ := le_streamMaximum (fun i => streamMaximum _ (score i)) u

/-- Rank computed by querying scalar coefficients of the weighted Gram determinant. -/
def rankQuery [DecidableEq K] (M : Matrix (Fin n) (Fin m) K) : ℕ :=
  scanRank n m (determinantQuery (weightedGramEntryCoeff M))

end WeightedGramQuery

theorem rankQuery_eq {K : Type*} [Field K] [DecidableEq K] {n m : ℕ} (M : Matrix (Fin n) (Fin m) K) :
    rankQuery M = M.rank :=
  scanRank_correct M _ (determinantQuery_eq (weightedGram M) _ (weightedGramEntryCoeff_eq M))

end RankQuery

end VPVNP
end Computability
end OAI
