import OAI.Computability.VPVNP.FixedNativeProgram
import OAI.Computability.VPVNP.PaperPairParameters
import OAI.Computability.VPVNP.LiveProgramWordFit

/-!
# A common word-capacity threshold for the literal program

The operand vector is fixed before choosing the input length. Identifying
the rational bucket exponents identifies the whole live geometry, so the
verified intermediate word bounds apply directly to this literal program.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM Compression LiveProgram CursorNetwork Filter RAMTape

variable {K : Type*} [Field K] {S : BlockSchedule K} (D : FixedProgramDiagonal.Program)
    (B : S.Templates) (u : PairExponents B.growthConstant)

theorem paperGeometry_eq (hnumerator : D.numerator = (liveRatio u).num)
    (hdenominator : D.denominator = (liveRatio u).den) (n : ℕ) :
    D.geometry n = paperGeometry D.addressFactor (liveCapacity u) n := by
  unfold geometry paperGeometry liveCapacity
  rw [hnumerator,hdenominator]

private theorem transport {k w : ℕ} (args : Fin k → InputOperand) {actual paper : Geometry}
    (geom : actual = paper) (width : paper.w = w)
    (fits : ∀ j, (InputOperandMachine.geometryOnly args j).Fits paper (2^w)) :
    ∀ j, (InputOperandStartup.Expr args j).Fits actual (2^actual.w) := by
  subst actual
  subst w
  exact fits

attribute [local irreducible] Pieces.count rows LiveProgram.operand InputOperandMachine.geometryOnly PublicExpr.Fits

theorem eventually_operandFits (hnumerator : D.numerator = (liveRatio u).num)
    (hdenominator : D.denominator = (liveRatio u).den) :
    ∀ᶠ n : ℕ in atTop, D.OperandFits n := by
  apply (eventually_operand_geometry_fits D.constants D.evaluator D.pair D.address_pos
    (liveCapacity_polynomial u)).mono
  intro n fits
  exact transport D.operands (paperGeometry_eq D B u hnumerator hdenominator n) rfl fits

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
