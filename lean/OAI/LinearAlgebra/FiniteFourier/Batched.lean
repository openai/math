import OAI.LinearAlgebra.FiniteFourier.CircuitParallel
import OAI.LinearAlgebra.FiniteFourier.Transform
import OAI.LinearAlgebra.FiniteFourier.FeedbackBorder

/-! # Independent finite abelian Fourier transforms

Enumeration by `Fin n` lets different groups and different transform directions share
one matrix format. Gates of a circuit for the resulting matrix may mix all copies.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

universe u v
noncomputable section
open scoped BigOperators

/-- One order-`n` transform over a common splitting field, in arbitrary coordinates. -/
structure FourierBlock (K : Type v) [Field K] (n : ℕ) where
  G : Type u
  [group : AddCommGroup G]
  [finiteGroup : Fintype G]
  admissible : Admissible G K
  points : Fin n ≃ G
  frequencies : Fin n ≃ Character G K
  inverse : Bool

attribute [instance] FourierBlock.group FourierBlock.finiteGroup

variable {K : Type v} [Field K] {n J : ℕ}

namespace FourierBlock

theorem card_group (B : FourierBlock K n) : Fintype.card B.G = n := by
  simpa using Fintype.card_congr B.points.symm

/-- The selected forward or normalized inverse transform in the given coordinates. -/
def matrix (B : FourierBlock K n) : Matrix (Fin n) (Fin n) K :=
  if B.inverse then
    Matrix.reindex B.points.symm B.frequencies.symm (inverseFourierMatrix B.G K)
  else
    Matrix.reindex B.frequencies.symm B.points.symm (fourierMatrix B.G K)

/-- A splitting field supplies an enumeration of the characters at every group order. -/
def ofGroup (G : Type u) [AddCommGroup G] [Fintype G] (h : Admissible G K)
    (hn : Fintype.card G = n) (inverse : Bool) : FourierBlock K n where
  G := G
  admissible := h
  points := (Fintype.equivFinOfCardEq hn).symm
  frequencies := (Fintype.equivFinOfCardEq ((card_character G K h).trans hn)).symm
  inverse := inverse

end FourierBlock

/-- The direct sum of the selected transforms. Circuit gates may mix all batch indices. -/
def batchMatrix (B : Fin J → FourierBlock K n) : Matrix (Fin n × Fin J) (Fin n × Fin J) K :=
  Matrix.blockDiagonal (fun j => (B j).matrix)

theorem complexity_batchMatrix_le_sum (B : Fin J → FourierBlock K n) :
    complexity (batchMatrix B) ≤ ∑ j, complexity (B j).matrix :=
  (complexity_le_iff _ _).2 <|
    RealizableAtMost.blockDiagonal_family (fun j => realizableAtMost_complexity (B j).matrix)

/-- Number of nonzero entries of the whole transfer, including cross-block entries. -/
def matrixEntryCount {I O F : Type*} [Fintype I] [Fintype O] [Zero F] (Z : Matrix O I F) : ℕ := by
  classical
  exact (Finset.univ.filter (fun ij : O × I => Z ij.1 ij.2 ≠ 0)).card

/-- Joint Zariski closure of a feedback transfer plus a rank error and an entrywise
sparse error. Both errors act on the whole matrix, including across batch indices. -/
def JointErrorBorderAtMost {I O : Type*} [Fintype I] [Fintype O]
    (M : Matrix O I K) (S : ℕ) (rankBudget supportBudget : ℝ) : Prop := by
  classical
  exact ∀ p : MvPolynomial (O × I) (AlgebraicClosure K),
    (∀ A B Z : Matrix O I (AlgebraicClosure K), FeedbackAtMost A S →
      (B.rank : ℝ) ≤ rankBudget →
      (matrixEntryCount Z : ℝ) ≤ supportBudget →
      MvPolynomial.eval (fun ij => (A + B + Z) ij.1 ij.2) p = 0) →
    MvPolynomial.eval (fun ij => algebraMap K (AlgebraicClosure K) (M ij.1 ij.2)) p = 0

/-- Enlarging either global budget preserves joint-border membership. -/
theorem JointErrorBorderAtMost.mono {I O : Type*} [Fintype I] [Fintype O]
    {M : Matrix O I K} {S : ℕ} {r r' t t' : ℝ} (h : JointErrorBorderAtMost M S r t)
    (hr : r ≤ r') (ht : t ≤ t') : JointErrorBorderAtMost M S r' t' := by
  intro p hp
  exact h p fun A B Z hA hB hZ => hp A B Z hA (hB.trans hr) (hZ.trans ht)

theorem GeometricBorderAtMost.jointError {I O : Type*} [Fintype I] [Fintype O]
    {M : Matrix O I K} {S : ℕ} (h : GeometricBorderAtMost M S)
    {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) : JointErrorBorderAtMost M S r t := by
  classical
  intro p hp
  apply h p
  intro A hA
  simpa using hp A 0 0 hA (by simpa using hr) (by simpa [matrixEntryCount] using ht)

end
end FiniteFourier
end LinearAlgebra
end OAI
