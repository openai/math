import OAI.Computability.VPVNP.CompressorLabelEvaluator
import OAI.Computability.VPVNP.CountedLabelReadback
import OAI.Computability.VPVNP.ParseOracleResources

/-!
# Coefficient queries for the grammar and the two compressor templates

The fixed sparse row table contains both the six-party shrink equations and
the port-graph refresh equations. The word-indexed rows use the two counted
Boolean-circuit queries. The integer row result applies to every input word
and every formal exponent vector.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

open MvPolynomial JointLabelSystem RadicalCertificate.MonomialIndex

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates) {n : ℕ}

/-- The scalar function in the dense bounded-monomial matrix interface. -/
noncomputable abbrev compressorCoeff (hn : 2 ≤ n) (c : ℕ) :=
  FixedRows.countedCoeff B.Entry B.EquationIndex B.equation hn c

theorem compressorCoeff_eq (hn : 2 ≤ n) (c : ℕ)
    (i : Fin (2 ^ n + Fintype.card B.EquationIndex)) (a : Fin (B.compressorLabelCount c n) → ℕ) :
    B.compressorCoeff hn c i a = (B.compressorEquations hn c (FixedRows.rowIndex B.EquationIndex n i)).coeff
      (exponentVector a) := FixedRows.countedCoeff_eq B.Entry B.EquationIndex B.equation hn c i a

/-- The label-coordinate order table fits polynomial advice even when the
two template families have different party and label types. -/
theorem compressorOrderAdvice_polynomial (c : ℕ) :
    PolynomiallyBounded (fun n => FixedRows.orderBits B.Entry n c) :=
  FixedRows.orderBits_polynomiallyBounded B.Entry c

/-- Polynomial bounds for the circuit advice, stack capacity, and exponent of
the execution time of the dense production histogram lookup. -/
theorem compressorParseResources_polynomial (c : ℕ) :
    PolynomiallyBounded (fun n => ParseOracle.adviceBound c n (FixedRows.productionCount n c) (2*n)) ∧
    PolynomiallyBounded (fun n => ParseOracle.stackBound c n (FixedRows.productionCount n c) (2*n)) ∧
    PolynomiallyBounded (fun n => ParseOracle.timeExponent c n (FixedRows.productionCount n c) (2*n)) := by
  have hS : PolynomiallyBounded (fun n => FixedRows.productionCount n c) :=
    (FixedRows.labelTotal_polynomiallyBounded Unit c).of_le fun n => by
      rw [← FixedRows.labelOrder_length]
      exact Nat.le_add_right ..
  have hw : PolynomiallyBounded (fun n => 2*n) := (PolynomiallyBounded.const 2).mul .id
  exact ⟨ParseOracle.adviceBound_polynomial c hS hw, ParseOracle.stackBound_polynomial c hS hw,
    ParseOracle.timeExponent_polynomial c hS hw⟩

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
