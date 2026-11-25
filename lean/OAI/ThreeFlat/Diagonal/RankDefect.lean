import OAI.LinearAlgebra.SpectralBooks.KroneckerRank
import OAI.ThreeFlat.RankError
import OAI.ThreeFlat.Diagonal.DefectBudget

namespace OAI
/-! # Rank loss in the block replacement of a catalytic computation

Fixing all replaceable strings in a block leaves a rank-one matrix on the
touched indices and an identity on the other external indices. We bound the
error from replacing the scalar identity on the catalyst, including summation
over fixings, ordered multiplication of blocks and restriction of endpoints.
-/

namespace ThreeFlat.Diagonal

open scoped BigOperators Kronecker

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- For a fixed summand the remaining identity multiplies the catalyst error
by its dimension. The touched external chunks and auxiliary register are
described by one outer product. -/
theorem fixing_rank_defect {τ υ : Type*} [Fintype τ] [Fintype υ] [DecidableEq υ]
    (u v : τ → K) (A X : Matrix ι ι K) :
    (((Matrix.vecMulVec u v ⊗ₖ (1 : Matrix υ υ K)) ⊗ₖ A) -
      ((Matrix.vecMulVec u v ⊗ₖ (1 : Matrix υ υ K)) ⊗ₖ X)).rank ≤
      Fintype.card υ * (A - X).rank := by
  let E := Matrix.vecMulVec u v ⊗ₖ (1 : Matrix υ υ K)
  have h : (E ⊗ₖ A) - (E ⊗ₖ X) = E ⊗ₖ (A - X) := by
    ext i j
    exact (mul_sub _ _ _).symm
  rw [show ((Matrix.vecMulVec u v ⊗ₖ (1 : Matrix υ υ K)) ⊗ₖ A) -
      ((Matrix.vecMulVec u v ⊗ₖ (1 : Matrix υ υ K)) ⊗ₖ X) = E ⊗ₖ (A - X) from h,
    LinearAlgebra.SpectralBooks.rank_kronecker]
  apply Nat.mul_le_mul_right
  simpa only [E, LinearAlgebra.SpectralBooks.rank_kronecker, Matrix.rank_one, one_mul] using
    Nat.mul_le_mul_right (Fintype.card υ) (Matrix.rank_vecMulVec_le (R := K) u v)

/-- Summing at most `s.card` fixings per block and then restricting boundary
indices costs at most the number of blocks times the single-block budget. -/
theorem restricted_block_defect {σ β γ : Type*} [Fintype γ]
    (steps : List β) (s : Finset σ) (A B : β → σ → Matrix ι ι K)
    (r : γ → ι) (m : ℕ) (bound : ∀ t ∈ steps, ∀ j ∈ s, (A t j - B t j).rank ≤ m) :
    (((steps.map fun t => ∑ j ∈ s, A t j).prod.submatrix r r) -
      ((steps.map fun t => ∑ j ∈ s, B t j).prod.submatrix r r)).rank ≤
      steps.length * (s.card * m) := by
  classical
  apply (rank_sub_restricted_blocks_le steps (fun _ => s) A B r r).trans
  induction steps with
  | nil => simp
  | cons t rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    rw [Nat.add_comm (rest.length * _)]
    apply Nat.add_le_add
    · calc
        _ ≤ ∑ _j ∈ s, m := Finset.sum_le_sum fun j hj => bound t (by simp) j hj
        _ = _ := by simp
    · apply ih
      intro t ht j hj
      exact bound t (by simp [ht]) j hj

/-- The matrix for one fixing of a block. The two index maps identify which
physical coordinates are touched by the fixing and which serve as the
untouched memory. They may vary from block to block. -/
def fixingMatrix {τ υ κ : Type*} [DecidableEq υ]
    (r c : ι → (τ × υ) × κ) (u v : τ → K) (M : Matrix κ κ K) : Matrix ι ι K :=
  (((Matrix.vecMulVec u v ⊗ₖ (1 : Matrix υ υ K)) ⊗ₖ M).submatrix r c)

/-- Sum all fixings, compose the blocks in order, and fix the auxiliary
coordinates at both endpoints. -/
noncomputable def blockedComputation {β σ τ υ κ γ : Type*} [DecidableEq υ]
    (steps : List β) (s : Finset σ) (rows cols : β → σ → ι → (τ × υ) × κ)
    (u v : β → σ → τ → K) (M : β → σ → Matrix κ κ K) (external : γ → ι) :
    Matrix γ γ K :=
  ((steps.map fun t => ∑ j ∈ s, fixingMatrix (rows t j) (cols t j)
    (u t j) (v t j) (M t j)).prod).submatrix external external

private theorem rank_sub_comm {κ : Type*} [Fintype κ] (A X : Matrix κ κ K) :
    (A - X).rank = (X - A).rank := by
  simpa only [neg_one_smul, neg_sub] using
    Matrix.rank_smul_of_mem_nonZeroDivisors (X - A)
      (mem_nonZeroDivisors_of_ne_zero (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0)))

/-- The block replacement bound in the diagonal approximation lemma. Each
fixing has a rank-one touched factor. Its two versions differ only on the
catalyst, where the scalar identity has been approximated with error at most
`e` in rank. -/
theorem block_replacement_rank {β σ τ υ κ γ : Type*}
    [Fintype τ] [Fintype υ] [DecidableEq υ] [Fintype κ] [DecidableEq κ] [Fintype γ]
    (steps : List β) (s : Finset σ) (rows cols : β → σ → ι → (τ × υ) × κ)
    (u v : β → σ → τ → K) (z : β → σ → K) (X : β → σ → Matrix κ κ K)
    (external : γ → ι) (e : ℕ)
    (approx : ∀ t ∈ steps, ∀ j ∈ s, (X t j - z t j • (1 : Matrix κ κ K)).rank ≤ e) :
    let run := fun M => blockedComputation steps s rows cols u v M external
    (run (fun t j => z t j • (1 : Matrix κ κ K)) - run X).rank ≤
        steps.length * (s.card * (Fintype.card υ * e)) := by
  apply restricted_block_defect
  intro t ht j hj
  let fixed := Matrix.vecMulVec (u t j) (v t j) ⊗ₖ (1 : Matrix υ υ K)
  change (((fixed ⊗ₖ (z t j • (1 : Matrix κ κ K))) - (fixed ⊗ₖ X t j)).submatrix
    (rows t j) (cols t j)).rank ≤ _
  exact (Matrix.rank_submatrix_le _ _ _).trans
    ((fixing_rank_defect _ _ _ _).trans
      (Nat.mul_le_mul_left (Fintype.card υ)
        ((rank_sub_comm _ _).le.trans (approx t ht j hj))))

/-- A full identity shift cannot result from replacing blocks whose total
rank defect is smaller than the external dimension. -/
theorem ne_identity_add_of_rank_defect (A B : Matrix ι ι K)
    (h : (A - B).rank < Fintype.card ι) : A ≠ 1 + B := by
  rintro rfl
  simp at h

/-- For the paper's tick count and polynomial block size, the replaced
computation cannot differ from the original by the external identity.
`c` is the catalyst width, `B` the external width. -/
theorem diagonal_replacement_ne_identity_add {β σ τ υ κ γ : Type*}
    [Fintype τ] [Fintype υ] [DecidableEq υ] [Fintype κ] [DecidableEq κ]
    [Fintype γ] [DecidableEq γ] (steps : List β) (s : Finset σ)
    (rows cols : β → σ → ι → (τ × υ) × κ) (u v : β → σ → τ → K)
    (z : β → σ → K) (X : β → σ → Matrix κ κ K) (external : γ → ι)
    {w d L c B : ℕ} (hw : d + 8 ≤ w) (hL : L ≤ w ^ d)
    (hsave : 2 ^ (w ^ 3) * 2 ^ (w ^ 10 - w) ≤ c) (hc : c ≤ B)
    (nsteps : steps.length ≤ 2 ^ (w ^ 6) / L)
    (nfix : s.card ≤ 2 ^ (4 * L * 2 ^ (w ^ 10 - w ^ 4)))
    (nrem : Fintype.card υ ≤ 2 ^ (B - c)) (ndim : Fintype.card γ = 2 ^ B)
    (approx : ∀ t ∈ steps, ∀ j ∈ s, (X t j - z t j • (1 : Matrix κ κ K)).rank ≤
      2 ^ (c - 2 ^ (w ^ 3) * 2 ^ (w ^ 10 - w))) :
    let run := fun M => blockedComputation steps s rows cols u v M external
    run (fun t j => z t j • (1 : Matrix κ κ K)) ≠ 1 + run X := by
  apply ne_identity_add_of_rank_defect
  rw [ndim]
  apply lt_of_le_of_lt (block_replacement_rank steps s rows cols u v z X external _ approx)
  let save := 2 ^ (w ^ 3) * 2 ^ (w ^ 10 - w)
  have hcatalyst : Fintype.card υ * 2 ^ (c - save) ≤ 2 ^ (B - save) := by
    calc
      _ ≤ 2 ^ (B - c) * 2 ^ (c - save) := Nat.mul_le_mul_right _ nrem
      _ = _ := by
        rw [← Nat.pow_add]
        congr 1
        dsimp only [save]
        omega
  exact lt_of_le_of_lt (Nat.mul_le_mul nsteps (Nat.mul_le_mul nfix hcatalyst))
    (by simpa only [Nat.mul_assoc] using defect_dimension_budget hw hL (hsave.trans hc))

end ThreeFlat.Diagonal

end OAI
