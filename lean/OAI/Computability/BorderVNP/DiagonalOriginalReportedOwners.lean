import OAI.Computability.BorderVNP.DiagonalCandidatePublishedOwners
import OAI.Computability.BorderVNP.DiagonalReturnedCandidateStages

/-! The cells of the original returned candidate read their registered owners after sparse emission. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Lean Meta Elab Term

/-- Specialize the sparse owner read to the publication and the opening of a single returned
candidate. The two projections jointly identify all the native circuit and program parameters. -/
private def returnedOwnerRead (levels : List Level) (inputs : Array Expr) : TermElabM Expr := do
  let method := Lean.mkConst ``CandidateReportPublication.proposedOwnersOnReturn levels
  forallTelescope (← inferType method) fun args _ => do
    let names ← args.mapM fun arg => arg.fvarId!.getUserName
    let mut values : Std.HashMap FVarId Expr := {}
    for (key, projection) in [(`K, ``ReturnedCandidateReports.toPublication),
        (`opening, ``ReturnedCandidateReports.toOpening)] do
      let some i := names.idxOf? key | throwError "missing original owner-read input {key}"
      let projected := mkAppN (Lean.mkConst projection levels) inputs
      let pattern ← inferType args[i]!
      let observed ← inferType projected
      for (formal, actual) in pattern.getAppArgs.zip observed.getAppArgs do
        if formal.isFVar then values := values.insert formal.fvarId! actual
      values := values.insert args[i]!.fvarId! projected
    let some stop := names.idxOf? `ownerAt | throwError "missing the registered owner's word"
    let native ← (args.extract 0 stop).mapM fun arg => do
      let some value := values.get? arg.fvarId! |
        throwError "missing the original owner-read parameter {← arg.fvarId!.getUserName}"
      return value
    return mkAppN method native

open Lean.Elab.Command in
run_cmd liftTermElabM do
  let prior ← getConstInfo ``ReturnedCandidateReports.toOpening
  let levels := prior.levelParams.map Level.param
  let proof ← forallTelescope prior.type fun inputs _ => do
    mkLambdaFVars inputs (← returnedOwnerRead levels inputs)
  let name := `OAI.Computability.BorderVNP.RoutingISA.Evaluator.SignedPrep.ReturnedCandidateReports.ownersOnOriginalReturn
  addDecl (.thmDecl { name, levelParams := prior.levelParams, type := ← inferType proof, value := proof })
  addDocStringCore name "Every emitted row of the returned candidate reads its registered routed owner, using the publication and opening of that same return."

/-- Read the original native coordinates directly from the returned candidate's dependent type. -/
elab "originalReportedOwners% " obtained:term:max registered:term:max : term => do
  let actual ← elabTerm obtained none
  let some report ← whnfUntil (← inferType actual) ``ReturnedCandidateReports |
    throwError "expected the original returned candidate reports"
  let method := Lean.mkConst ``ReturnedCandidateReports.ownersOnOriginalReturn report.getAppFn.constLevels!
  let read := mkAppN method (report.getAppArgs.push actual)
  return mkApp read (← elabTerm registered none)

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
