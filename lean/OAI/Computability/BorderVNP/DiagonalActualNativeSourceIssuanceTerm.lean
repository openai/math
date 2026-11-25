import OAI.Computability.BorderVNP.DiagonalOriginalSnapshotPlannerTerm

/-! # Issuance from a returned native source

The selected lookup, replay, source equality and private return carry the
coordinates of the issuer. Read the coordinates from those records together
so that the returned bank, memory and two costs belong to the same trace.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term TeamContraction PackedHistoryCircuit
open RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep

private abbrev SourceArguments := Std.HashMap FVarId Expr

private def headed (term : Expr) (name : Name) : MetaM Expr := do
  let some result ← whnfUntil term name | throwError "expected {name} in the native issuance"
  return result

/-- Match the parameters of two applications of the same declaration. Some
parameters, such as the report label, are computed expressions and are read
from their own record instead. -/
private def readArguments (known : SourceArguments) (pattern actual : Expr)
    (head : Name) : MetaM SourceArguments := do
  let formals := (← headed pattern head).getAppArgs
  let values := (← headed actual head).getAppArgs
  unless formals.size == values.size do throwError "incompatible {head} applications"
  let mut result := known
  for (formal,value) in formals.zip values do
    if formal.isFVar && !result.contains formal.fvarId! then
      result := result.insert formal.fvarId! value
  return result

private def findArgument (args : Array Expr) (name : Name) : MetaM Expr := do
  let some field ← args.findM? fun x => return (← x.fvarId!.getUserName) == name
    | throwError "unknown native issuance parameter {name}"
  return field

private def atParameter (application : Expr) (field : Name) : MetaM Expr := do
  let args := application.getAppArgs
  forallTelescope (← inferType application.getAppFn) fun formals _ => do
    let some i ← formals.findIdxM? fun x => return (← x.fvarId!.getUserName) == field
      | throwError "unknown {field} in {application.getAppFn.constName?}"
    unless i < args.size do throwError "unsaturated native source record"
    return args[i]!

/-- The nine words shared across the lookups occur in the site's attained
snapshot. The original extension contains the previous word bank and the
geometry destination. -/
private def setupWords (lookup : Expr) : MetaM (Array (Name × Expr)) := do
  let evidence := lookup.getAppArgs.back!
  forallBoundedTelescope (← inferType evidence) (some 3) fun site _ => do
    let reached ← headed (mkAppN evidence site) ``Exists
    withLocalDeclD `trace reached.getAppArgs[0]! fun trace => do
      let seen ← headed (mkApp reached.getAppArgs[1]! trace) ``And
      let snapshot ← headed seen.getAppArgs[0]! ``CandidateSite.OnReturn
      let old ← headed (← atParameter snapshot `old) ``routingExtension
      let extension ← headed (← atParameter old `old) ``RoutingISA.SignedTaskArena.Layout.extension
      let mut words := #[(`previous, extension.getAppArgs.back!), (`origin, ← atParameter old `origin)]
      for (parameter,source) in #[(`fresh,`fresh), (`geomGates,`gates), (`outputs,`outputs),
          (`field,`width), (`off,`off), (`ell,`ell), (`literalCtl,`controls)] do
        words := words.push (parameter, ← atParameter snapshot source)
      let bound := (site.push trace).map (·.fvarId!)
      for (_,word) in words do
        let free := (collectFVars {} word).fvarSet
        if bound.any (fun x => free.contains x) then throwError "a setup word varies across the selected sites"
      return words

private def checkedWord (lookup : Expr) : MetaM Expr := do
  let word ← atParameter lookup `word
  let value ← withReducible <| whnfHeadPred word fun e =>
    pure (match e with | .proj ``Subtype 0 _ => false | _ => !e.isAppOf ``Subtype.val)
  match value with
  | .proj ``Subtype 0 checked => return mkProj ``Subtype 1 checked
  | e =>
    unless e.isAppOfArity ``Subtype.val 3 do throwError "expected the value of the checked declaration"
    return mkProj ``Subtype 1 e.getAppArgs.back!

/-- Supply the native original-prefix issuer at its actual registered target.
The arguments are the selected site, its checked replay, the original source
identity, its report observation, the funded roster, the seven numerical
issuance facts, the finite axis, the returned frame equality and the planner
layout equality. The claim and proposed reports come from the goal. -/
elab "exactNativeSourceIssuance% " site:term:max ", " replay:term:max ", " source:term:max ", "
    observed:term:max ", " funded:term:max ", " numbers:term:max ", " coordinate:term:max ", "
    atFrame:term:max ", " layout:term:max : term <= wanted => do
  let chosen ← elabTerm site none
  let reached ← elabTerm replay none
  let identity ← elabTerm source none
  let observation ← elabTerm observed none
  let roster ← elabTerm funded none
  let facts ← elabTerm numbers none
  let axis ← elabTerm coordinate none
  let frame ← elabTerm atFrame none
  let selected ← headed (← inferType chosen) ``PreparationFrame.SelectedLookupSites
  let registered ← headed wanted ``RegisteredOriginalPrefix
  let returnType ← headed registered.getAppArgs.back! ``Cube.Physical.NativeLedger.OriginalPrefixRun
  let numerical := fun (i : Nat) =>
    let tail := (List.range i).foldl (fun term _ => mkProj ``And 1 term) facts
    if i < 6 then mkProj ``And 0 tail else tail
  let addresses := numerical 2
  let allocated := numerical 0
  let marks := numerical 1
  let marked := mkApp4 (mkConst ``And.intro) (← inferType allocated) (← inferType marks) allocated marks
  let issuerName := ``PreparationFrame.SelectedLookupSites.issueSourcePrefixAtFrameOfReads
  let info ← getConstInfo issuerName
  let level :: _ := selected.getAppFn.constLevels! | throwError "missing the selected-site universe"
  let issuerType := info.type.instantiateLevelParams info.levelParams [level]
  let ordered ← forallTelescope issuerType fun parameters target => do
    let formal := findArgument parameters
    let mut known : SourceArguments := {}
    for (parameter,actual,head) in #[
        (`chosen,chosen,``PreparationFrame.SelectedLookupSites),
        (`reached,reached,``PreparationFrame.CandidateReportsOnReplay),
        (`addresses,addresses,``RoutingISA.SignedTaskArena.Layout.FinishAddresses)] do
      known ← readArguments known (← inferType (← formal parameter)) (← inferType actual) head
    let left ← headed (← inferType (← formal `identified)) ``Eq
    let right ← headed (← inferType identity) ``Eq
    known ← readArguments known left right ``Eq
    known ← readArguments known left.getAppArgs.back! right.getAppArgs.back! ``PreparationFrame.sourceOwnedAt
    let goal ← headed target ``RegisteredOriginalPrefix
    let original ← headed goal.getAppArgs.back! ``Cube.Physical.NativeLedger.OriginalPrefixRun
    known ← readArguments known original returnType ``Cube.Physical.NativeLedger.OriginalPrefixRun
    known ← readArguments known (← atParameter original `a) (← atParameter returnType `a)
      ``Cube.Physical.NativeAssignments.rawPath
    let explicit := (← setupWords selected) ++ #[
      (`chosen,chosen), (`reached,reached), (`identified,identity), (`returned,observation),
      (`roster,roster), (`axis,axis), (`atFrame,frame), (`valid,← checkedWord selected),
      (`addresses,addresses), (`allocated,marked), (`values,numerical 3), (`cubeRoom,numerical 4),
      (`cap,numerical 5), (`ids,numerical 6)]
    for (key,val) in explicit do known := known.insert (← formal key).fvarId! val
    parameters.mapM fun param => do
      return (← param.fvarId!.getUserName, known[param.fvarId!]?)
  -- Elaborate the caller's snapshot in the original local context.
  let mut args := #[]
  let mut remaining := issuerType
  for (name,value) in ordered do
    let arg ← match value with
    | some term => pure term
    | none =>
      let domain := remaining.bindingDomain!.instantiateRev args
      if name == `snapshots then
        elabTermEnsuringType (← `(actualSnapshotWithPlannerEq% $site, $layout)) domain
      else if #[`cube,`baseRoom,`teamCount,`dest].contains name then
        let eqn ← headed domain ``Eq
        mkEqRefl eqn.getAppArgs[1]!
      else throwError "missing native issuance parameter {name}"
    args := args.push arg
    remaining := remaining.bindingBody!
  return mkAppN (mkConst issuerName [level]) args

end Diagonal

end BorderVNP
end Computability
end OAI
