import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenReadback

/-! # Transporting a returned placement to the observed public frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal
open Lean Meta Elab Term FiniteEvaluator

private theorem atRecordedFrame {H : OpenSuffix.Inputs} {a : RoutingISA.CubeArena.Layout}
    {before : DiagonalTallyAllocation.BeforeTasks} {base actual : ℕ} {memory : ℕ → ℕ}
    (frame : actual=base) (placement : OpenSuffix.Placement H a before base memory) :
    OpenSuffix.Placement H a before actual memory := by
  cases frame
  exact placement

/-- Transport the actual placement of an issued entry to the observed public
frame, keeping its original arena, control stage, report tables, and memory. -/
elab "originalPaidPlacement%" source:term:max : term => do
  let entry ← elabTerm source none
  let frame ← mkProjection entry `frame
  let stored ← mkProjection entry `placement
  let some eq ← whnfUntil (← inferType frame) ``Eq | throwError "expected the opened frame equality"
  let some p ← whnfUntil (← inferType stored) ``OpenSuffix.Placement | throwError "expected a stored placement"
  let #[section_,arena,tables,base,memory] := p.getAppArgs | throwError "unexpected placement operands"
  return mkAppN (Lean.mkConst ``atRecordedFrame) #[section_,arena,tables,base,eq.getAppArgs[1]!,memory,frame,stored]
end Diagonal

end BorderVNP
end Computability
end OAI
