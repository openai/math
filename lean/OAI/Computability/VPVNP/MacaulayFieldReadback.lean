import OAI.Computability.VPVNP.MacaulayReadBlocks
import OAI.Computability.VPVNP.MacaulayPairEntries
import OAI.Computability.VPVNP.AffinePinCoefficient
import OAI.Computability.VPVNP.RankCoordinateSliceMinors

/-! # Coefficients of the actual matrix requested by the rank machine

The physical reader encodes elements of the advised finite field in a power
basis. Each row in the augmented matrix has exactly the coefficient described
by its shifted or powered branch, with the zero scalar on failed exponent
tests. The Cramer query uses this same encoded matrix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead

open RadicalCertificate.MonomialIndex Coordinate.SliceMinors SliceArithmetic

variable {F : Type} [Field F] {p e t eqs : ℕ} [Fact p.Prime] [NeZero e]
variable [Algebra (ZMod p) F] {c : Vector p e} (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] F)

private theorem encode_zero : AffinePin.Query.encode φ 0 = 0 := by
  apply (φ.injective.comp (Scalar.interpret_injective c))
  change φ (Scalar.interpretation c (AffinePin.Query.encode φ 0)) = φ (Scalar.interpretation c 0)
  rw [AffinePin.Query.value_encode, map_zero, map_zero]

private theorem encode_one : AffinePin.Query.encode φ 1 = 1 := by
  apply (φ.injective.comp (Scalar.interpret_injective c))
  change φ (Scalar.interpretation c (AffinePin.Query.encode φ 1)) = φ (Scalar.interpretation c 1)
  rw [AffinePin.Query.value_encode, map_one, map_one]

variable [Fact (Irreducible (modulus c))] (Q : QueryData t eqs F)

/-- The original and affine rows differ only in their scalar coefficient
reader. Both use the multiplier and column monomial in this exact order. -/
theorem shifted_matrix_entry (row : Fin eqs) (o : Fin (size t Q.multiplierDegree)) (j : Fin (size t Q.columnDegree)) :
    let a := enumeration t Q.multiplierDegree o
    let b := enumeration t Q.columnDegree j
    baseMatrix φ Q ((finProdFinEquiv (row,o)).castAdd (size t Q.pointBound)) j =
      if a.val ≤ b.val then AffinePin.Query.encode φ (Q.getCoeff row (fun i => b.val i - a.val i)) else 0 := by
  intro a b
  change AffinePin.Query.encode φ (appendRows Q.equations Q.monomials ((finProdFinEquiv (row,o)).castAdd _) j) = _
  simp only [appendRows, Fin.addCases_left, QueryData.equations, equationEntry, Equiv.symm_apply_apply,
    indexedDigits_eq]
  by_cases h : a.val ≤ b.val
  · rw [ite_eq_left h]
    have hc : ∀ i, (enumeration t Q.multiplierDegree o).val i ≤ (enumeration t Q.columnDegree j).val i := h
    rw [ite_eq_left hc]
  · rw [ite_eq_right h]
    have hc : ¬∀ i, (enumeration t Q.multiplierDegree o).val i ≤ (enumeration t Q.columnDegree j).val i := h
    rw [ite_eq_right hc, encode_zero]

/-- Encoding a powered monomial row over the slice field yields the same
zero/one coefficient as testing its exponents in the native scalar type. -/
theorem power_matrix_entry (o : Fin (size t Q.pointBound)) (j : Fin (size t Q.columnDegree)) :
    baseMatrix φ Q (o.natAdd (eqs*size t Q.multiplierDegree)) j =
      powerEntry (K := Scalar c) Q.power (indexedDigits o) j := by
  change AffinePin.Query.encode φ (appendRows Q.equations Q.monomials (o.natAdd _) j) = _
  simp only [appendRows, Fin.addCases_right, powerEntry]
  split_ifs
  · exact encode_one φ
  · exact encode_zero φ

end RankQuery.Stack.MacaulayRead

end VPVNP
end Computability
end OAI
