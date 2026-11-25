import OAI.Computability.BorderVNP.DiagonalCalendarOriginalFieldGeometry
import OAI.Computability.BorderVNP.DiagonalCalendarRegisteredSiteOperator
import OAI.Computability.BorderVNP.DiagonalCalendarRouteInputsOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarCommonFrame
import OAI.Computability.BorderVNP.DiagonalHostHeaderAtFrameTerm
import OAI.Computability.BorderVNP.DiagonalHostPublicationAtSiteTerm

/-! # Private layout capacity and routing header on the original report family -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term TeamContraction
open private selectedStage slottedReturn from OAI.Computability.BorderVNP.DiagonalHostPublicationAtSiteTerm
open private startupHeader from OAI.Computability.BorderVNP.DiagonalHostHeaderAtFrameTerm

set_option maxRecDepth 22000
set_option maxHeartbeats 22000000
set_option cleanup.letToHave false

private def indexedArguments (name : Name) (args : Array Expr) : MetaM (NameMap Expr) := do
  let mut signature := (← getConstInfo name).type
  let mut inputs : NameMap Expr := {}
  for value in args do
    let .forallE binder _ next _ := signature | throwError "unexpected argument to {name}"
    inputs := inputs.insert binder value
    signature := next
  return inputs

private def frameAt (inputs : NameMap Expr) (team : Expr) : MetaM Expr := do
  let name := ``SignedCalendarAt.frozenSites_frame
  let info ← getConstInfo name
  let mut signature := info.type
  let mut args := #[]
  while signature.isForall do
    let key := signature.bindingName!
    let value ← if key == `u then pure team
      else if signature.bindingInfo!.isInstImplicit then synthInstance (signature.bindingDomain!.instantiateRev args)
      else match inputs.find? key with
        | some argument => pure argument
        | none => throwError "missing frame coordinate {key}"
    args := args.push value
    signature := signature.bindingBody!
  return mkAppN (mkConst name (info.levelParams.map fun _ => Level.zero)) args

private def recordSetup {claim : Prop} (proof : claim) : PSigma fun statement : Prop => statement :=
  ⟨claim, proof⟩

private def hostSetupOnReports : MetaM Expr :=
  SignedCalendarAt.withCheckedRouteOperands ``SignedCalendarAt.routeInputsOnOriginalReports fun inputs calibrated => do
    let geometry ← SignedCalendarAt.certifyOnCheckedCalendar
      ``SignedCalendarAt.registeredPhysicalOnOriginalSelection inputs calibrated
    let owners := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuedOwnershipAtOriginalOfCandidates) calibrated
    let readback := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.routeReadbackOnOriginalReports) inputs
    let coordinates ← indexedArguments ``SignedCalendarAt.FrozenRouteChecks calibrated
    let service ← withLocalDeclD `f (← SignedCalendarAt.nextIssuedInput geometry) fun f => do
      let selection ← SignedCalendarAt.selectIssuedSite readback geometry f
      let some selected ← whnfUntil (← inferType selection) ``PreparationFrame.SelectedLookupSites |
        throwError "expected the selected field's original sites"
      let some owner ← whnfUntil (← inferType (mkApp owners f)) ``PreparationFrame.ReturnedOwnershipAt |
        throwError "expected the original returned ownership"
      let ownerArgs ← indexedArguments ``PreparationFrame.ReturnedOwnershipAt owner.getAppArgs
      let some exterior := ownerArgs.find? `origin | throwError "missing the original returned exterior"
      let placed := mkApp2 geometry f selection
      withLocalDeclD `t (← SignedCalendarAt.nextIssuedInput placed) fun team => do
        let physical := mkProj ``And 0 (mkApp placed team)
        let header := mkProj ``And 0 physical
        let pin := mkProj ``And 1 (mkProj ``And 1 physical)
        let site := selectedStage selected selection exterior team ``PreparationFrame.SelectedLookupSites.returnedSite
        let result ← TermElabM.run' do
          let returned ← slottedReturn pin site
          let fits := mkProj ``And 0 (mkProj ``And 1 returned)
          let common ← startupHeader (← frameAt coordinates team) header
          return mkAppN (mkConst ``And.intro) #[← inferType fits, ← inferType common, fits, common]
        mkLambdaFVars #[f, team] result
    return mkAppN (mkConst ``recordSetup) #[← inferType service, service]

local elab "hostSetupOnReports%" : term => hostSetupOnReports

/-- Each issued field and team has room for the private layout in its reached geometry. Its
routing header uses the actual startup frame, as required by the host-source reader. -/
noncomputable def SignedCalendarAt.hostSetupOnOriginalReports := hostSetupOnReports%

end Diagonal

end BorderVNP
end Computability
end OAI
