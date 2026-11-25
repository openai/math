import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenReadback
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsBundle

/-! # Reading a returned bundle at its observed host frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term FiniteEvaluator DiagonalTallyCellReports

private theorem atReturnedHost (P : ℕ → Prop) {base actual : ℕ}
    (frame : actual = base) (stored : P base) : P actual := by
  cases frame
  exact stored

/-- Keep the reports, bundle table, bit widths and room proof, changing only the
frame used by the cable copy to read the delivered bundle. -/
private def hostAtReturnedEntry (entry stored : Expr) : MetaM Expr := do
  let frame ← mkProjection entry `frame
  let some frameEq ← whnfUntil (← inferType frame) ``Eq
    | throwError "expected the returned control entry's frame equation"
  let #[_, actual, base] := frameEq.getAppArgs | throwError "unexpected frame equation"
  forallBoundedTelescope (← inferType stored) (some 2) fun js result => do
    unless js.size = 2 do throwError "expected the bundle and its presence"
    let some parts ← whnfUntil result ``And | throwError "expected delivery and site room"
    let #[words, room] := parts.getAppArgs | throwError "unexpected delivery and room"
    let some delivered ← whnfUntil words ``ReportBundle.delivered
      | throwError "expected the delivered bundle"
    let #[bundle, layout, description, image] := delivered.getAppArgs
      | throwError "unexpected bundle receipt"
    let some host ← whnfUntil image ``OpenSuffix.hostImage
      | throwError "expected the recorded host memory"
    let #[_, memory] := host.getAppArgs | throwError "unexpected host memory"
    let motive ← withLocalDeclD `cursor (mkConst ``Nat) fun cursor => do
      let imageAt := mkApp2 host.getAppFn cursor memory
      let received := mkAppN delivered.getAppFn #[bundle,layout,description,imageAt]
      let visits ← mkForallFVars js (mkApp2 parts.getAppFn received room)
      mkLambdaFVars #[cursor] visits
    return mkAppN (Lean.mkConst ``atReturnedHost) #[motive,base,actual,frame,stored]

/-- Read the registered bundle at the actual frame of its returned control entry. -/
elab "originalHostedAtEntry%" entry:term:max stored:term:max : term => do
  hostAtReturnedEntry (← elabTerm entry none) (← elabTerm stored none)

end Diagonal

end BorderVNP
end Computability
end OAI
