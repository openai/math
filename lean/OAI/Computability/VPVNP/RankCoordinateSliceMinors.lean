import OAI.Computability.VPVNP.RankCoordinateSliceReader
import OAI.Computability.VPVNP.RankCoordinateReplacement

/-! # Encoded entries and selected minors of a slice coordinate query -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.SliceMinors

open SliceArithmetic RadicalCertificate.MonomialIndex RadicalCertificate.MonomialIndex.QueryData
open FiniteSlice RAMTape

variable {F : Type} [Field F] [DecidableEq F] {p e t eqs : ℕ} [Fact p.Prime] [NeZero e]
    [Algebra (ZMod p) F] {c : Vector p e} [Fact (Irreducible (modulus c))]
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] F) (data : QueryData t eqs F)

/-- Packs the extension-field coordinates of a field element into the scalar representation
used by the entry reader. -/
noncomputable def encode (x : F) : Scalar c := Scalar.pack c (scalarEncoding φ x)

omit [DecidableEq F] in
theorem decode_encode (x : F) : (φ.toRingEquiv.toRingHom.comp (Scalar.interpretation c)) (encode φ x) = x := by
  change φ (value (modulus c) (Scalar.pack c (scalarEncoding φ x)).digits) = _
  rw [Scalar.digits_pack,map_scalarEncoding]

/-- The Macaulay relation matrix with the monomial rows appended below the equation rows. -/
abbrev fieldMatrix := appendRows data.equations data.monomials
/-- Original row indices selected by the greedy independent-row scan of the appended matrix. -/
abbrev row := greedyRowIndex (fieldMatrix data)
/-- Original column indices forming the invertible coordinate minor of the greedy row basis. -/
abbrev col := coordinateColumns (greedyRowBasis (fieldMatrix data)) (greedyRowBasis_fullRank _)

/-- The appended matrix with every field entry packed as a scalar for the native reader. -/
noncomputable def baseMatrix := (fieldMatrix data).map (encode φ)
/-- The square Cramer denominator formed by restricting the encoded matrix to the chosen
independent rows and columns. -/
noncomputable def denominator := (baseMatrix φ data).submatrix (row data) (col data)
/-- The encoded target row for applying the given operation at one quotient-basis coordinate. -/
noncomputable def target (op : Operation t) (i : Fin data.dimension) := encode φ ∘ data.stepTarget op i
/-- The denominator minor with the row for the next coordinate replaced by the current target
on the selected columns. -/
noncomputable def numerator (op : Operation t) (i j : Fin data.dimension) :=
  (denominator φ data).updateRow (combinedOrdinal data.equations data.monomials j) (target φ data op i ∘ col data)

theorem denominator_map : (denominator φ data).map (φ.toRingEquiv.toRingHom.comp (Scalar.interpretation c)) =
    (greedyRowBasis (fieldMatrix data)).submatrix id (col data) := by
  ext i j; exact decode_encode φ _

theorem numerator_map (op : Operation t) (i j : Fin data.dimension) :
    (numerator φ data op i j).map (φ.toRingEquiv.toRingHom.comp (Scalar.interpretation c)) =
    replacedMinor (greedyRowBasis (fieldMatrix data)) (col data) (data.stepTarget op i)
      (combinedOrdinal data.equations data.monomials j) := by
  ext x y
  by_cases h : x = combinedOrdinal data.equations data.monomials j
  · subst x; simp [numerator,replacedMinor,target]; exact decode_encode φ _
  · simp [numerator,replacedMinor,h,Matrix.map_apply]
    exact decode_encode φ _

variable {K : Type} [DecidableEq K] {w v Br Bc Ba Bt S : ℕ}
    {rows cols : FiniteRoutine (OrdinalRead.Port K)} {scalar power : FiniteRoutine (MacaulayRead.Port K)}
    {ready : Stacks K → Prop}

omit [NeZero e] in
/-- The two scalar matrices consumed by the determinant roots are built from
the selected row and column addresses of the full indexed equation matrix. -/
theorem reads (op : Operation t) (i j : Fin data.dimension)
    (hr : OrdinalRead.CorrectSpace rows (row data) w Br S ready)
    (hc : OrdinalRead.CorrectSpace cols (col data) w Bc S ready)
    (ha : MacaulayRead.CorrectSpace scalar (baseMatrix φ data) w v Ba S ready)
    (ht : MacaulayRead.CorrectSpace power (fun _ j => target φ data op i j :
      Matrix (Fin (eqs * size t data.multiplierDegree + size t data.pointBound)) (Fin (size t data.columnDegree)) _) w v Bt S ready)
    (hfit : NativeReader.order data ≤ 2^w) :
    MacaulayRead.CorrectSpace (Submatrix.minorRead rows cols scalar) (denominator φ data) w v
      (Br+Bc+Ba+2*(w+1)) S (Submatrix.Ready ready) ∧
    MacaulayRead.CorrectSpace (Replacement.numerator (Submatrix.minorRead rows cols scalar) (Submatrix.minorRead rows cols power))
      (numerator φ data op i j) w v (20*w+10+(max (Br+Bc+Ba+2*(w+1)) (Br+Bc+Bt+2*(w+1))+1))
      (max S (w+(20*w+10))) (Replacement.Ready w (combinedOrdinal data.equations data.monomials j) (Submatrix.Ready ready)) := by
  exact ⟨Submatrix.correctSpace hr hc ha, Replacement.submatrix_correctSpace hr hc ha ht _ hfit⟩

end RankQuery.Stack.Coordinate.SliceMinors

end VPVNP
end Computability
end OAI
