import OAI.Computability.BorderVNP.FiniteEvaluatorCubeStopWord

/-! # Using the dimensions of a returned evaluator's address bound -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term

/-- Recover the evaluator, word width and three dimensions from a proof
that its end address fits in a word. -/
def reportedEndAddressOperands (bounded : Expr) : MetaM (Array Expr) := do
  let some comparison ← whnfUntil (← inferType bounded) ``LT.lt
    | throwError "expected a strict address bound"
  let #[_, _, left, _] := comparison.getAppArgs | throwError "unexpected address comparison"
  let some address ← whnfUntil left ``RoutingISA.SignedTaskArena.Layout.endAddress
    | throwError "expected the evaluator's end address"
  let parameters := address.getAppArgs
  unless parameters.size == 5 do
    throwError "expected the evaluator, word width and three address dimensions"
  return parameters

/-- Apply the cube's address bound with the dimensions stored in the return. -/
elab "cubeStopAtReportedEnd% " measured:term:max : term => do
  let bounded ← elabTerm measured none
  let parameters ← reportedEndAddressOperands bounded
  return mkAppN (mkConst ``RoutingISA.SignedTaskArena.Layout.cube_stop_lt_word) (parameters.push bounded)

end Diagonal

end BorderVNP
end Computability
end OAI
