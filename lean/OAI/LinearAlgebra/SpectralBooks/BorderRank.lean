import OAI.LinearAlgebra.SpectralBooks.Tensor
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Geometric border rank

We use equations of the affine Zariski closure in a fixed tensor format. Both
the polynomials and the rank decompositions tested by their equations are
taken over the algebraic closure of the ground field.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation

noncomputable section

variable {F X Y Z : Type*} [Field F]

/-- The scalar extension of a tensor, entry by entry. -/
def toAlgebraicClosure (T : Tensor F X Y Z) : Tensor (AlgebraicClosure F) X Y Z :=
  fun x y z => algebraMap F (AlgebraicClosure F) (T x y z)

/-- Evaluate a polynomial in the tensor entries. -/
def tensorEval (T : Tensor F X Y Z) : MvPolynomial (X × Y × Z) F →+* F :=
  MvPolynomial.eval (fun p => T p.1 p.2.1 p.2.2)

/-- Membership in the Zariski closure of the rank-at-most-`r` locus after scalar extension. -/
def GeometricBorderRankAtMost (T : Tensor F X Y Z) (r : ℕ) : Prop :=
  ∀ p : MvPolynomial (X × Y × Z) (AlgebraicClosure F),
    (∀ S : Tensor (AlgebraicClosure F) X Y Z, S.RankAtMost r → tensorEval S p = 0) →
      tensorEval (toAlgebraicClosure T) p = 0

theorem geometricBorderRankAtMost_of_rankAtMost {T : Tensor F X Y Z} {r : ℕ}
    (h : T.RankAtMost r) : GeometricBorderRankAtMost T r := by
  exact fun p hp => hp _ (h.map (algebraMap F (AlgebraicClosure F)))

/-- A determinant of coordinate entries is a polynomial in the tensor. -/
private theorem eval_minor {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (S : Tensor K X Y Z) (entry : I → I → X × Y × Z) :
    tensorEval S (Matrix.of (fun i j =>
      MvPolynomial.X (entry i j) : I → I → MvPolynomial (X × Y × Z) K)).det =
    (Matrix.of fun i j => S (entry i j).1 (entry i j).2.1 (entry i j).2.2).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [tensorEval]

variable [Fintype X] [Fintype Y]

private theorem exists_geometricBorderRankAtMost (T : Tensor F X Y Z) :
    ∃ r, GeometricBorderRankAtMost T r :=
  ⟨_, geometricBorderRankAtMost_of_rankAtMost (rankAtMost_tensorRank T)⟩

/-- The least rank whose locus has the scalar-extended tensor in its Zariski closure. -/
def geometricBorderRank (T : Tensor F X Y Z) : ℕ := by
  classical
  exact Nat.find (exists_geometricBorderRankAtMost T)

theorem geometricBorderRankAtMost_geometricBorderRank (T : Tensor F X Y Z) :
    GeometricBorderRankAtMost T (geometricBorderRank T) := by
  classical
  exact Nat.find_spec (exists_geometricBorderRankAtMost T)

theorem geometricBorderRank_le_of_atMost {T : Tensor F X Y Z} {r : ℕ}
    (h : GeometricBorderRankAtMost T r) : geometricBorderRank T ≤ r := by
  classical
  exact Nat.find_min' (exists_geometricBorderRankAtMost T) h

theorem geometricBorderRank_le_tensorRank (T : Tensor F X Y Z) :
    geometricBorderRank T ≤ tensorRank T :=
  geometricBorderRank_le_of_atMost (geometricBorderRankAtMost_of_rankAtMost (rankAtMost_tensorRank T))

/-- A nonzero minor whose determinant vanishes on tensors of insufficient
rank supplies a lower bound on geometric border rank. -/
theorem card_le_geometricBorderRank_of_minor {I : Type*} [Fintype I] [DecidableEq I]
    (T : Tensor F X Y Z) (entry : I → I → X × Y × Z)
    (hne : (Matrix.of fun i j => T (entry i j).1 (entry i j).2.1 (entry i j).2.2).det ≠ 0)
    (hvanish : ∀ (S : Tensor (AlgebraicClosure F) X Y Z) (r : ℕ), S.RankAtMost r →
      r < Fintype.card I →
      (Matrix.of fun i j => S (entry i j).1 (entry i j).2.1 (entry i j).2.2).det = 0) :
    Fintype.card I ≤ geometricBorderRank T := by
  by_contra! hlt
  let p := (Matrix.of (fun i j => MvPolynomial.X (entry i j) :
    I → I → MvPolynomial (X × Y × Z) (AlgebraicClosure F))).det
  have he := geometricBorderRankAtMost_geometricBorderRank T p (fun S hS => by
    rw [show tensorEval S p = _ from eval_minor S entry]
    exact hvanish S _ hS hlt)
  rw [show tensorEval (toAlgebraicClosure T) p = _ from eval_minor _ entry] at he
  let A : Matrix I I F := Matrix.of fun i j => T (entry i j).1 (entry i j).2.1 (entry i j).2.2
  change ((algebraMap F (AlgebraicClosure F)).mapMatrix A).det = 0 at he
  rw [← RingHom.map_det] at he
  exact hne ((map_eq_zero _).mp he)

end

end SpectralBooks
end LinearAlgebra
end OAI
