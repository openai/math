import OAI.Computability.BorderVNP.DiagonalCalendarIssuedHostInstaller
import OAI.Computability.BorderVNP.DiagonalOriginalOwnerReplayTerm
import OAI.Computability.BorderVNP.DiagonalSelectedLookupSites

/-! # Installing the original host reader at its observed registered route -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term TeamContraction
open private replayParameters replayParameter from OAI.Computability.BorderVNP.DiagonalOriginalOwnerReplayTerm

private def sourceReader (issued : Expr) : TermElabM Expr := do
  let name := ``SignedCalendarAt.frozenIssuedHostSource
  unless issued.isAppOf name do throwError "expected the calibrated host reader"
  forallTelescope (← getConstInfo name).type fun parameters _ => do
    let mut afterValues := false
    for i in [:parameters.size] do
      let binder ← parameters[i]!.fvarId!.getUserName
      if afterValues && binder == `hist then
        return mkAppN issued.getAppFn (issued.getAppArgs.extract 0 (i+1))
      afterValues := binder == `values
    throwError "missing the model history on the host reader"

/-- Install the reader on the original returned rows and symbols at team zero. The handoff
supplies the actual delivery, table-entry identifiers and row count. The two final arguments
are the matching assignment and its observation on the same registered route. -/
elab "originalHostLedger% " issued:term:max sites:term:max rows:term:max writer:term:max
    symbols:term:max handoff:term:max matched:term:max observed:term:max : term => do
  let reader ← sourceReader (← elabTerm issued none)
  let selected ← replayParameters (← elabTerm sites none) ``PreparationFrame.SelectedLookupSites
  let hand ← elabTerm handoff none
  let inputs ← replayParameters hand ``OwnedHandoff
  let delivery ← replayParameter inputs `f
  let sent ← replayParameters delivery ``ReturnedDelivery
  let mut fields := inputs
  for (input, source) in [(`x, `ext), (`route, `L), (`in₀, `pin), (`hist, `H), (`owner, `owner)] do
    fields := fields.insert input (← replayParameter sent source)
  for index in [`ib, `hb, `sb] do
    fields := fields.insert index (← replayParameter selected index)
  fields := fields.insert `delivery delivery |>.insert `recordCount (← replayParameter inputs `count)
    |>.insert `owned (← elabTerm rows none) |>.insert `writer (← elabTerm writer none)
    |>.insert `symbols (← elabTerm symbols none) |>.insert `handoff hand
  let route ← elabTerm matched none
  let receipt ← elabTerm observed none
  forallBoundedTelescope (← whnf (← inferType reader)) (some 21) fun parameters _ => do
    let mut args := #[]
    for parameter in parameters do
      let binder ← parameter.fvarId!.getDecl
      let value ← if binder.userName == `anchor then
        elabTerm (← `(0)) (some (binder.type.replaceFVars (parameters.extract 0 args.size) args))
        else replayParameter fields binder.userName
      args := args.push value
      if binder.userName == `handoff then return mkAppN reader (args ++ #[route, receipt])
    throwError "missing the observed handoff on the original host reader"

end Diagonal

end BorderVNP
end Computability
end OAI
