import OAI.Optimization.LinearProgramming.Compression.Mass
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The integer polynomial belonging to a minor, before its matrix entries are evaluated. -/

open scoped BigOperators

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

/-- The determinant on a selected array of variables. An entry can occur more than once. -/
noncomputable def symbolicMinor {σ : Type*} {k : ℕ} (entry : Fin k → Fin k → σ) :
    MvPolynomial σ ℤ :=
  Matrix.det (Matrix.of fun i j => MvPolynomial.X (entry i j))

/-- Evaluation commutes with forming the minor, over an arbitrary commutative ring. -/
theorem eval_symbolicMinor {σ R : Type*} [CommRing R] {k : ℕ}
    (entry : Fin k → Fin k → σ) (v : σ → R) :
    MvPolynomial.eval₂Hom (Int.castRingHom R) v (symbolicMinor entry) =
      Matrix.det (Matrix.of fun i j => v (entry i j)) := by
  rw [symbolicMinor, RingHom.map_det]
  congr 1
  ext i j
  exact MvPolynomial.eval₂Hom_X' _ _ _

/-- Every permutation contributes a product of exactly `k` variables. -/
theorem totalDegree_symbolicMinor_le {σ : Type*} {k : ℕ} (entry : Fin k → Fin k → σ) :
    (symbolicMinor entry).totalDegree ≤ k := by
  classical
  rw [symbolicMinor, Matrix.det_apply]
  refine MvPolynomial.totalDegree_finsetSum_le fun π _ => ?_
  have hp : (∏ i, (MvPolynomial.X (entry (π i) i) : MvPolynomial σ ℤ)).totalDegree ≤ k := by
    simpa using MvPolynomial.totalDegree_finsetProd Finset.univ
      (fun i => (MvPolynomial.X (entry (π i) i) : MvPolynomial σ ℤ))
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simpa [h] using hp

/-- The signs preserve mass and there are `k!` permutation monomials. -/
theorem coeffMass_symbolicMinor_le {σ : Type*} {k : ℕ} (entry : Fin k → Fin k → σ) :
    coeffMass (symbolicMinor entry) ≤ k.factorial := by
  classical
  rw [symbolicMinor, Matrix.det_apply]
  apply (mass_sum_le ..).trans
  calc
    _ ≤ ∑ _ : Equiv.Perm (Fin k), 1 := by
      apply Finset.sum_le_sum
      intro π _
      have hp : coeffMass (∏ i, (MvPolynomial.X (entry (π i) i) : MvPolynomial σ ℤ)) ≤ 1 := by
        simpa using mass_prod_le Finset.univ
          (fun i => (MvPolynomial.X (entry (π i) i) : MvPolynomial σ ℤ))
      rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simpa [h] using hp
    _ = k.factorial := by simp [Fintype.card_perm]

/-- Increasing row and column selections give each unordered choice of a square minor once. -/
abbrev SquareMinorIndex (rows cols : ℕ) :=
  Σ k : Fin (cols + 1), (Fin k.val ↪o Fin rows) × (Fin k.val ↪o Fin cols)

noncomputable instance squareMinorIndexFintype (rows cols : ℕ) : Fintype (SquareMinorIndex rows cols) := by
  classical
  letI (k r : ℕ) : Fintype (Fin k ↪o Fin r) :=
    Fintype.ofInjective (fun e : Fin k ↪o Fin r => (e : Fin k → Fin r)) DFunLike.coe_injective
  unfold SquareMinorIndex
  infer_instance

/-- A minor can come from either of the two input matrices. -/
abbrev PairMinorIndex (rD rE n : ℕ) := SquareMinorIndex rD n ⊕ SquareMinorIndex rE n

/-- Independent indeterminates for all entries of the two matrices. -/
abbrev PairVariable (rD rE n : ℕ) := (Fin rD ⊕ Fin rE) × Fin n

theorem card_pairVariable {rD rE n : ℕ} (h : rD + rE = n) :
    Fintype.card (PairVariable rD rE n) = n ^ 2 := by
  simp [PairVariable, h, pow_two]

noncomputable def pairMinorPolynomial {rD rE n : ℕ} :
    PairMinorIndex rD rE n → MvPolynomial (PairVariable rD rE n) ℤ
  | .inl ⟨_, row, col⟩ => symbolicMinor fun i j => (Sum.inl (row i), col j)
  | .inr ⟨_, row, col⟩ => symbolicMinor fun i j => (Sum.inr (row i), col j)

noncomputable def pairMinorValue {R : Type*} [CommRing R] {rD rE n : ℕ}
    (D : Matrix (Fin rD) (Fin n) R) (E : Matrix (Fin rE) (Fin n) R) :
    PairMinorIndex rD rE n → R
  | .inl ⟨_, row, col⟩ => (D.submatrix row col).det
  | .inr ⟨_, row, col⟩ => (E.submatrix row col).det

/-- The valuation shared by all minors uses one field value per matrix entry. -/
def pairValuation {R : Type*} {rD rE n : ℕ}
    (D : Matrix (Fin rD) (Fin n) R) (E : Matrix (Fin rE) (Fin n) R)
    (x : PairVariable rD rE n) : R :=
  Sum.elim (fun i => D i x.2) (fun i => E i x.2) x.1

theorem eval_pairMinorPolynomial {R : Type*} [CommRing R] {rD rE n : ℕ}
    (D : Matrix (Fin rD) (Fin n) R) (E : Matrix (Fin rE) (Fin n) R)
    (u : PairMinorIndex rD rE n) :
    MvPolynomial.eval₂Hom (Int.castRingHom R) (pairValuation D E) (pairMinorPolynomial u) =
      pairMinorValue D E u := by
  rcases u with ⟨k, row, col⟩ | ⟨k, row, col⟩ <;> exact eval_symbolicMinor _ _

theorem totalDegree_pairMinorPolynomial_le {rD rE n : ℕ} (u : PairMinorIndex rD rE n) :
    (pairMinorPolynomial u).totalDegree ≤ n := by
  rcases u with ⟨k, row, col⟩ | ⟨k, row, col⟩ <;>
    exact (totalDegree_symbolicMinor_le _).trans (Nat.le_of_lt_succ k.isLt)

theorem coeffMass_pairMinorPolynomial_le {rD rE n : ℕ} (u : PairMinorIndex rD rE n) :
    coeffMass (pairMinorPolynomial u) ≤ n.factorial := by
  rcases u with ⟨k, row, col⟩ | ⟨k, row, col⟩ <;>
    exact (coeffMass_symbolicMinor_le _).trans (Nat.factorial_le (Nat.le_of_lt_succ k.isLt))

end Compression
end LinearProgramming
end Optimization
end OAI
