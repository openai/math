import OAI.Computability.BorderVNP.DiagonalCalendarFrozenReportK
import OAI.Computability.BorderVNP.DiagonalSelectedLookupBuilders

/-! # Forming the frozen report certificate from its selected frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term TeamContraction RoutingISA.Evaluator.SignedPrep

private def instanceSlot (parameter : LocalDecl) : MetaM Name := do
  if !parameter.binderInfo.isInstImplicit then return parameter.userName
  unless parameter.type.isAppOf ``Fintype do
    throwError "unexpected instance parameter in the selected report"
  let type := parameter.type.appArg!
  return Name.str `fintypeFor (← type.fvarId!.getUserName).toString

private def reportParams (type : Expr) (head : Name) : MetaM (Expr × NameMap Expr) := do
  let some app ← whnfUntil type head | throwError "expected {head} in the selected report"
  let info ← getConstInfo head
  forallTelescope info.type fun ps _ => do
    let mut args : NameMap Expr := {}
    for p in ps, v in app.getAppArgs do
      args := args.insert (← instanceSlot (← p.fvarId!.getDecl)) v
    return (app,args)

private def reportArg (args : NameMap Expr) (key : Name) : MetaM Expr := do
  let some arg := args.find? key | throwError "missing {key} in the selected report"
  return arg

private partial def staticKWithInventory (provider index : TSyntax `term) : TermElabM Expr := do
  match provider with
  | `(($t)) => staticKWithInventory t index
  | `($fn $args*) => elabTerm (← `($fn $args* (I := $index))) none
  | _ => throwError "expected the frozen calibration and history application"

private def frozenKSpine (provider : TSyntax `term) (fixed word site frame : Expr) : TermElabM Expr := do
  let (_,fr) ← reportParams (← inferType frame) ``PreparationFrame
  forallBoundedTelescope (← inferType site) (some 2) fun inputs result => do
    unless inputs.size == 2 do throwError "expected an exterior and team for the selected site"
    let (_,atSite) ← reportParams result ``CandidateSite
    let mut args : NameMap Expr := {}
    for n in [`L,`pin,`pub,`mac,`reg,`mem] do
      args := args.insert n (← reportArg fr n)
    args := args.insert `broadcastHeader (← reportArg fr `header)
    for n in [`X,`pp,`lp,`group,`I,`sizes,Name.str `fintypeFor "I"] do
      args := args.insert n (← reportArg atSite n)
    for (target,source) in [(`representative,`owner),(`initialBase,`frame),(`receiving,`receivingBase),
        (`resides,`host),(`keyID,`key)] do
      args := args.insert target (← reportArg atSite source)
    let team := inputs[1]!
    for (target,source) in [(`pinSites,`pins),(`broadcastFrame,`f),(`guess,`guess)] do
      args := args.insert target (← mkLambdaFVars #[team] (← reportArg atSite source))
    args := args.insert `inputFields (← mkLambdaFVars inputs (← reportArg atSite `fields))
      |>.insert `fixed fixed |>.insert `raw word |>.insert `site site |>.insert `frame frame
    let index ← exprToSyntax (← reportArg atSite `I)
    let providerExpr ← staticKWithInventory provider index
    let op := ``SignedCalendarAt.frozenReportK
    let info ← getConstInfo op
    forallTelescope info.type fun binders _ => do
      let keys ← binders.mapM fun b => b.fvarId!.getUserName
      let some hist := keys.idxOf? `hist | throwError "expected a frozen-history parameter"
      let actual := providerExpr.getAppArgs
      unless actual.size > hist do throwError "supply the calibration, values and history"
      let static := actual.extract 0 (hist+1)
      let later ← (binders.extract (hist+1) keys.size).mapM fun b => do
        instanceSlot (← b.fvarId!.getDecl)
      unless later[0]? == some `X && later.back? == some `frame do
        throwError "expected the original site and frame of the frozen report: {later}"
      let fn := Lean.mkConst op [← getDecLevel (← reportArg atSite `I)]
      let applied ← later.mapM fun key => do
        let arg ← reportArg args key
        return arg
      return mkAppN (mkAppN fn static) applied

private def keepLookupParameters (s : Expr) (op : Name) : MetaM Expr := do
  let (head, args) ← reportParams (← inferType s) ``PreparationFrame.SelectedLookupSites
  let info ← getConstInfo op
  forallTelescope info.type fun binders _ => do
    let mut applied := #[]
    for p in binders do
      let key ← instanceSlot (← p.fvarId!.getDecl)
      if key == `chosen then return mkApp (mkAppN (Lean.mkConst op head.getAppFn.constLevels!) applied) s
      applied := applied.push (← reportArg args key)
    throwError "expected the chosen lookup argument"

/-- Use the return family and its preparation frame to specialize the frozen
certificate with the exact inventory and physical input functions. -/
elab "frozenReportKAtSite%" provider:term:max fixed:term:max word:term:max site:term:max frame:term:max : term => do
  frozenKSpine provider (← elabTerm fixed none) (← elabTerm word none)
    (← elabTerm site none) (← elabTerm frame none)

/-- Form the same certificate directly on the issued lookup, retaining the
enumerations with which its sites and preparation frame were selected. -/
elab "frozenReportKAtLookup%" provider:term:max fixed:term:max word:term:max lookup:term:max : term => do
  let s ← elabTerm lookup none
  let site ← keepLookupParameters s ``PreparationFrame.SelectedLookupSites.returnedSite
  let frame ← keepLookupParameters s ``PreparationFrame.SelectedLookupSites.installedFrame
  frozenKSpine provider (← elabTerm fixed none) (← elabTerm word none) site frame

end Diagonal

end BorderVNP
end Computability
end OAI
