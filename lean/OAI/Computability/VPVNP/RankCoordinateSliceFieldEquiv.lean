import OAI.Computability.VPVNP.RankCoordinateFieldEquiv
import OAI.Computability.VPVNP.RankCoordinateSliceMinors
import OAI.Computability.VPVNP.RankCoordinateSelectedMinor

/-!
# Identifying the native and advised index sets of the slice minors

The native rank code selects rows and columns after interpreting packed
scalars in the polynomial-basis extension. The query data selects them in
the advised field. The field isomorphism identifies both sets, including
the dense ordinal of the row replaced in the numerator.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack

open RAMTape

theorem OrdinalRead.CorrectSpace.castOrdinal {K : Type} [DecidableEq K] {r' r n w B S : ℕ}
    {read : FiniteRoutine (OrdinalRead.Port K)} {f : Fin r' → Fin n} {g : Fin r → Fin n} {ready : Stacks K → Prop}
    (hread : OrdinalRead.CorrectSpace read f w B S ready) (eq : r' = r) (hf : ∀ i, f i = g (Fin.cast eq i)) :
    OrdinalRead.CorrectSpace read g w B S ready := by
  subst r'
  exact (show f = g from funext hf) ▸ hread

theorem MacaulayRead.CorrectSpace.castSquare {K : Type} [DecidableEq K] {r' r w v B S p e : ℕ}
    {c : SliceArithmetic.Vector p e} {read : FiniteRoutine (MacaulayRead.Port K)} {ready : Stacks K → Prop}
    {N : Matrix (Fin r') (Fin r') (Scalar c)} {M : Matrix (Fin r) (Fin r) (Scalar c)}
    (hread : MacaulayRead.CorrectSpace read N w v B S ready) (eq : r' = r)
    (hN : ∀ i j, N i j = M (Fin.cast eq i) (Fin.cast eq j)) :
    MacaulayRead.CorrectSpace read M w v B S ready := by
  subst r'
  exact (show N = M from Matrix.ext hN) ▸ hread

private theorem row_eq_of_map_eq {L F : Type*} [Field L] [Field F] [DecidableEq L] [DecidableEq F] {n m : ℕ}
    (φ : L ≃+* F) (M : Matrix (Fin n) (Fin m) L) (N : Matrix (Fin n) (Fin m) F)
    (h : N = M.map φ) (hr : rankQuery N = rankQuery M) (i : Fin (rankQuery N)) :
    greedyRowIndex N i = greedyRowIndex M (Fin.cast hr i) := by
  subst N
  exact greedyRowIndex_map φ M i

private theorem col_eq_of_map_eq {L F : Type*} [Field L] [Field F] [DecidableEq L] [DecidableEq F] {n m : ℕ}
    (φ : L ≃+* F) (M : Matrix (Fin n) (Fin m) L) (N : Matrix (Fin n) (Fin m) F)
    (h : N = M.map φ) (hr : rankQuery N = rankQuery M) (i : Fin (rankQuery N)) :
    coordinateColumns (greedyRowBasis N) (greedyRowBasis_fullRank N) i =
      coordinateColumns (greedyRowBasis M) (greedyRowBasis_fullRank M) (Fin.cast hr i) := by
  subst N
  exact greedyColumns_map φ M i

namespace Coordinate.SliceMinors

open SliceArithmetic RadicalCertificate.MonomialIndex RadicalCertificate.MonomialIndex.QueryData

variable {F : Type} [Field F] [DecidableEq F] {p e t eqs : ℕ} [Fact p.Prime] [NeZero e]
    [Algebra (ZMod p) F] {c : Vector p e} [Fact (Irreducible (modulus c))]
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] F) (data : QueryData t eqs F)

/-- The encoded base matrix after interpreting each scalar in the polynomial extension field. -/
noncomputable abbrev interpretedMatrix := (baseMatrix φ data).map (Scalar.interpretation c)

omit [DecidableEq F] in
/-- Reading the physical scalar followed by its ring interpretation produces
the inverse image of the queried matrix entry in the advised field. -/
theorem interpretedMatrix_eq : interpretedMatrix φ data = (fieldMatrix data).map φ.symm := by
  ext i j
  apply φ.injective
  exact (decode_encode φ ((fieldMatrix data) i j)).trans (φ.apply_symm_apply _).symm

variable [DecidableEq (AdjoinRoot (modulus c))]

theorem interpretedRank : rankQuery (interpretedMatrix φ data) = rankQuery (fieldMatrix data) := by
  rw [interpretedMatrix_eq]
  exact rankQuery_map_eq φ.symm.toRingEquiv _

theorem interpretedRow (i : Fin (rankQuery (interpretedMatrix φ data))) :
    greedyRowIndex (interpretedMatrix φ data) i = row data (Fin.cast (interpretedRank φ data) i) :=
  row_eq_of_map_eq φ.symm.toRingEquiv _ _ (interpretedMatrix_eq φ data) (interpretedRank φ data) i

theorem interpretedCol (i : Fin (rankQuery (interpretedMatrix φ data))) :
    SelectedMinor.cols (baseMatrix φ data) i = col data (Fin.cast (interpretedRank φ data) i) :=
  col_eq_of_map_eq φ.symm.toRingEquiv _ _ (interpretedMatrix_eq φ data) (interpretedRank φ data) i

/-- The next quotient coordinate's ordinal among all greedy basis rows, cast to the rank
computed over the extension field. -/
noncomputable abbrev nativeOrdinal (next : Fin data.dimension) :=
  Fin.cast (interpretedRank φ data).symm (combinedOrdinal data.equations data.monomials next)

theorem denominator_cast_apply (i j : Fin (rankQuery (interpretedMatrix φ data))) :
    SelectedMinor.selected (baseMatrix φ data) (baseMatrix φ data) i j =
      denominator φ data (Fin.cast (interpretedRank φ data) i) (Fin.cast (interpretedRank φ data) j) := by
  change baseMatrix φ data (greedyRowIndex (interpretedMatrix φ data) i) (SelectedMinor.cols (baseMatrix φ data) j) =
    baseMatrix φ data _ _
  rw [interpretedRow, interpretedCol]

theorem numerator_cast_apply (op : Operation t) (current next : Fin data.dimension)
    (i j : Fin (rankQuery (interpretedMatrix φ data))) :
    ((SelectedMinor.selected (baseMatrix φ data) (baseMatrix φ data)).updateRow (nativeOrdinal φ data next)
      (target φ data op current ∘ SelectedMinor.cols (baseMatrix φ data))) i j =
      numerator φ data op current next (Fin.cast (interpretedRank φ data) i) (Fin.cast (interpretedRank φ data) j) := by
  by_cases hi : i = nativeOrdinal φ data next
  · subst i
    simp only [numerator, nativeOrdinal, Fin.cast_cast, Fin.cast_refl, id_eq, Matrix.updateRow_self, Function.comp_apply]
    rw [interpretedCol]
  · have hfield : Fin.cast (interpretedRank φ data) i ≠ combinedOrdinal data.equations data.monomials next :=
      fun h => hi (Fin.ext (congrArg (fun i : Fin (rankQuery (fieldMatrix data)) => i.val) h))
    simp only [numerator, Matrix.updateRow_ne hi, Matrix.updateRow_ne hfield]
    exact denominator_cast_apply φ data i j

end Coordinate.SliceMinors
end RankQuery.Stack

end VPVNP
end Computability
end OAI
