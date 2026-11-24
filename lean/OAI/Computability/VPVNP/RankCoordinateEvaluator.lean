import OAI.Computability.VPVNP.MacaulaySliceBasis
import OAI.Computability.VPVNP.RankCoordinateColumn
import OAI.Computability.VPVNP.RankCoordinateCramer
import OAI.Computability.VPVNP.RankCoordinateReader

/-!
# From suffix coordinates to the evaluator's linear-step matrices

A step of the counting evaluator starts at the current basis ordinal and chooses
the next ordinal. Its scalar is the coefficient at the *next* ordinal in the
image of the *current* basis vector. This is the entry of the transpose of the
usual column-vector matrix. The indexed Cramer target therefore uses the current
basis monomial, and its queried row ordinal uses the next one.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex.QueryData

open RankQuery FiniteSlice
open RankQuery.Stack.Coordinate (combinedOrdinal)

variable {K : Type*} [Field K] [DecidableEq K] {t e : ℕ} (S : QueryData t e K)

/-- The row for the powered monomial obtained after acting on the current basis vector. -/
abbrev stepTarget (op : Operation t) (j : Fin S.dimension) : Fin (size t S.columnDegree) → K :=
  powerEntry S.power (S.target op (indexedDigits (S.basisIndex j)))

/-- Cramer scalar for the next basis coordinate after acting on the current vector. -/
def stepCoordinate (op : Operation t) (current next : Fin S.dimension) : K :=
  greedyCoordinateQuery (appendRows S.equations S.monomials) (S.stepTarget op current)
    (combinedOrdinal S.equations S.monomials next)

theorem matrixEntry_eq_greedyCoordinate (op : Operation t) (i j : Fin S.dimension) :
    S.matrixEntry op i j = greedyCoordinateQuery (appendRows S.equations S.monomials)
      (S.stepTarget op j) (combinedOrdinal S.equations S.monomials i) :=
  quotientCoordinate_at_suffix S.equations S.monomials (S.stepTarget op j) i

open RankQuery.Stack RankQuery.Stack.Coordinate SliceArithmetic

/-- The packed Cramer quotient has the correct value over the advised ground
field, even when that field is presented through an algebra equivalence. -/
theorem minorQuotient_eq_stepCoordinate {p deg : ℕ} [Fact p.Prime] [NeZero deg]
    [Algebra (ZMod p) K] (c : Vector p deg) [Fact (Irreducible (modulus c))]
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K) (op : Operation t)
    (current next : Fin S.dimension)
    (N D : Matrix (Fin (rankQuery (appendRows S.equations S.monomials)))
      (Fin (rankQuery (appendRows S.equations S.monomials))) (Scalar c))
    (hN : N.map (φ.toRingEquiv.toRingHom.comp (Scalar.interpretation c)) =
      replacedMinor (greedyRowBasis (appendRows S.equations S.monomials))
        (coordinateColumns _ (greedyRowBasis_fullRank _)) (S.stepTarget op current)
        (combinedOrdinal S.equations S.monomials next))
    (hD : D.map (φ.toRingEquiv.toRingHom.comp (Scalar.interpretation c)) =
      (greedyRowBasis (appendRows S.equations S.monomials)).submatrix id
        (coordinateColumns _ (greedyRowBasis_fullRank _))) :
    φ (value (modulus c) (Cramer.minorQuotient c N D)) = S.stepCoordinate op current next := by
  rw [Cramer.minorQuotient, value_mul, value_inverse, ← div_eq_mul_inv, map_div₀]
  exact topPencil_div_rowCoordinate (φ.toRingEquiv.toRingHom.comp (Scalar.interpretation c))
    N D _ _ _ _ hN hD

variable {E : Type*} [Field E] [Algebra K E] [Fintype K]

/-- The linear map whose transpose is used in the basis-index transition. -/
noncomputable def Operation.linearAction {A : Type*} [CommRing A] [Algebra K A]
    (op : Operation t) (X : Fin t → A) : A →ₗ[K] A :=
  match op with
  | .label i => LinearMap.mulLeft K (X i)
  | .frobenius => (FiniteField.frobeniusAlgHom K A).toLinearMap

variable [IsAlgClosed E] (F : Fin e → MvPolynomial (Fin t) K)

/-- The encoded ordinal width can present any natural number equal to the computed
slice dimension. The row-column ordering here is the order of evaluator transitions. -/
theorem stepCoordinate_eq_transition {D : ℕ} (hd : D = S.dimension)
    (h : S.Presents F) (b : Module.Basis (Fin D) K (CoordinateAlgebra K (points F E)))
    (hb : ∀ i, b i = S.listing F E (S.basisIndex (Fin.cast hd i))) (op : Operation t)
    (current next : Fin D) :
    S.stepCoordinate op (Fin.cast hd current) (Fin.cast hd next) =
      ((LinearMap.toMatrixAlgEquiv b) (op.linearAction (coordinateLabel (points F E)))).transpose
        current next := by
  subst D
  rw [stepCoordinate, ← S.matrixEntry_eq_greedyCoordinate op,
    S.matrixEntry_eq_repr F h b hb op, Matrix.transpose_apply, LinearMap.toMatrixAlgEquiv_apply]
  cases op with
  | label => rfl
  | frobenius =>
    simp [Operation.apply, Operation.linearAction, h.fieldOrder_eq, FiniteField.frobeniusAlgHom_apply]

end RadicalCertificate.MonomialIndex.QueryData

namespace RankQuery.Stack.Coordinate.Reader

open RAMTape SliceArithmetic Evaluator Evaluator.MatrixCallbacks FiniteSlice
open RadicalCertificate.MonomialIndex RadicalCertificate.MonomialIndex.QueryData

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {E : Type*} [Field E]
  [Algebra K E] [IsAlgClosed E] {t e : ℕ} {P : Type} [DecidableEq P]
  {p deg w v : ℕ} [Fact p.Prime] [Algebra (ZMod p) K] {c : Vector p deg}

/-- An actual returning suffix-coordinate program meets the evaluator's entry-reader
contract. Its packed result is identified by its value in the ground field, and its
registers and private bank are restored at the return. -/
theorem readsEntry_of_suffix (S : QueryData t e K) (F : Fin e → MvPolynomial (Fin t) K)
    (h : S.Presents F) (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K)
    (dim : BurstRAM.Word v) (hd : dim.val = S.dimension)
    (b : Module.Basis (Fin dim.val) K (CoordinateAlgebra K (points F E)))
    (hb : ∀ i, b i = S.listing F E (S.basisIndex (Fin.cast hd i)))
    (op : Operation t) (label time : ℕ) (extra : Stacks P) (core : FiniteRoutine (Port P))
    (query : ∀ current next : Fin dim.val, ∃ d ≤ time, ∃ a : Vector p deg,
      φ (value (modulus c) a) = S.stepCoordinate op (Fin.cast hd current) (Fin.cast hd next) ∧
      core.Runs d (bank (List.replicate label true) (ordinal dim current) (ordinal dim next) [] extra)
        (bank (List.replicate label true) (ordinal dim current) (ordinal dim next)
          (SliceArithmeticRound.packed w (List.ofFn a)) extra)) :
    ReadsEntry φ dim extra (install core) w label time
      ((LinearMap.toMatrixAlgEquiv b) (op.linearAction (coordinateLabel (points F E)))).transpose := by
  apply readsEntry
  intro current next
  obtain ⟨d, ht, a, hval, hr⟩ := query current next
  let T := ((LinearMap.toMatrixAlgEquiv b) (op.linearAction (coordinateLabel (points F E)))).transpose
  have hentry : φ (value (modulus c) a) = T current next :=
    hval.trans (S.stepCoordinate_eq_transition F hd h b hb op current next)
  have he : a = scalarEncoding φ (T current next) :=
    (valueEquiv c).injective (φ.injective (hentry.trans (map_scalarEncoding φ _).symm))
  refine ⟨d, ht, ?_⟩
  change core.Runs d _ (bank _ _ _ (SliceArithmeticRound.packed w
    (List.ofFn (scalarEncoding φ (T current next)))) extra)
  rw [← he]
  exact hr

end RankQuery.Stack.Coordinate.Reader

end VPVNP
end Computability
end OAI
