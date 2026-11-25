import OAI.Computability.BorderVNP.DiagonalCalendarNativePublicationPlacement

/-! # Applying the native placement theorem with a returned site's own indices -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term PackedHistoryCircuit

/-- Apply the placement theorem to one recorded return. Its published pin supplies
the network, its finite inventory and the execution parameters. Its two returned
machines supply the observed RAM and the epoch and directory publications. -/
elab "issuedNativePlacement%" calendar:term:max team:term:max pin:term:max record:term:max site:term:max : term => do
  let provider ← elabTerm calendar none
  let team ← elabTerm team none
  let pin ← elabTerm pin none
  let record ← elabTerm record none
  let site ← elabTerm site none
  let some source ← whnfUntil (← inferType pin) ``PublishedPin
    | throwError "expected the published native pin"
  let op := ``SignedCalendarAt.frozenNativePublicationPlacement
  let info ← getConstInfo op
  forallTelescope info.type fun binders _ => do
    let mut args := provider.getAppArgs
    let remaining := binders.extract args.size binders.size
    unless (← remaining[0]!.fvarId!.getUserName) == `dim do
      throwError "expected the calibrated planner task"
    let some pinBinder ← remaining.findM? fun b => return (← b.fvarId!.getUserName) == `pinReceipt
      | throwError "missing native pin receipt"
    let some model ← whnfUntil (← inferType pinBinder) ``PublishedPin
      | throwError "expected a native placement receipt"
    let mut values : FVarIdMap Expr := {}
    for arg in model.getAppArgs, actual in source.getAppArgs do
      if arg.isFVar then values := values.insert arg.fvarId! actual
    let mut observed : NameMap Expr := {}
    observed := observed.insert `team team |>.insert `pinReceipt pin
    for (key,carrier,field) in [(`literal,record,`oldWords), (`control,record,`controlBase),
        (`head,site,`origin), (`epoch,site,`epoch), (`publication,site,`published),
        (`geometry,record,`geometryMemory), (`middleEq,site,`epochMemory)] do
      observed := observed.insert key (← mkProjection carrier field)
    for (key,proof,side) in [(`literalWords,`literal,1), (`ctl,`control,1), (`frame,`head,1),
        (`seen,`geometry,1), (`middle,`middleEq,2)] do
      let some witness := observed.find? proof | throwError "missing recorded placement field {proof}"
      let some eqn ← whnfUntil (← inferType witness) ``Eq | throwError "expected a recorded equality"
      observed := observed.insert key eqn.getAppArgs[side]!
    for binder in remaining do
      let id := binder.fvarId!
      let name ← id.getUserName
      let some arg := (values.get? id).orElse (fun _ => observed.find? name)
        | throwError "the recorded pin leaves placement argument {name} unspecified"
      args := args.push arg
    return mkAppN (mkConst op provider.getAppFn.constLevels!) args

end Diagonal

end BorderVNP
end Computability
end OAI
