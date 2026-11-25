import OAI.Computability.BorderVNP.DiagonalCandidateReturnedFields

/-! # Applying the native candidate criteria to a physically returned scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Lean Meta Elab Term

/-- Supply the parameters of the existing admission theorem from the named
return proposition. Its two row functions also determine its row type. -/
private def returnedScanApplication (operation : Name) (proof : Syntax) : TermElabM Expr := do
  let proof ← elabTerm proof none
  let head := ``Diagonal.ReturnedWriterScan
  let some app ← whnfUntil (← inferType proof) head | throwError "expected the native returned writer scan"
  let args := app.getAppArgs
  let src ← getConstInfo head
  forallTelescope src.type fun binders _ => do
    let mut values : NameMap Expr := {}
    let mut inventory := none
    for binder in binders, arg in args do
      let decl ← binder.fvarId!.getDecl
      values := values.insert decl.userName arg
      if decl.binderInfo.isInstImplicit then inventory := some arg
    let some inventoryInstance := inventory | throwError "expected the scan's inventory instance"
    let info ← getConstInfo operation
    let fn := Lean.mkConst operation app.getAppFn.constLevels!
    forallTelescope info.type fun params _ => do
      let mut parameters := #[]
      for param in params do
        let decl ← param.fvarId!.getDecl
        if decl.userName == `source then return mkApp (mkAppN fn parameters) proof
        if decl.binderInfo.isInstImplicit then
          parameters := parameters.push inventoryInstance
        else
          let name := if decl.userName == `X then `exterior else decl.userName
          let some value := values.find? name | throwError "missing returned scan parameter {name}"
          parameters := parameters.push value
      throwError "expected the source argument of the scan admission theorem"

/-- The proved native admission function, specialized to the parameters of
this scan and applied to the scan itself. -/
elab "returnedScanAdmission%" proof:term:max : term =>
  returnedScanApplication ``CandidateSite.of_returned_writer_scan proof

/-- The proved admission and field-reindexing function, specialized to the
parameters of this returned scan. -/
elab "returnedScanFields%" proof:term:max : term =>
  returnedScanApplication ``CandidateSite.of_returned_scan_fields proof

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
