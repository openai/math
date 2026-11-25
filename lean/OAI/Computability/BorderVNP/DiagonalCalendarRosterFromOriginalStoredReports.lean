import OAI.Computability.BorderVNP.DiagonalCalendarCheckedOperation
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedReportRoster
import OAI.Computability.BorderVNP.DiagonalCalendarNativeNext
import OAI.Computability.BorderVNP.DiagonalCalendarSiteOnStoredOriginalReports

/-! # The registration roster of a stored original report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta RoutingISA.FragmentRows TeamContraction.ProcessorSlots

set_option maxRecDepth 28000
set_option maxHeartbeats 24000000

private def argumentNamed (value : Expr) (name : Name) : MetaM Expr := do
  let mut sig := (← getConstInfo value.getAppFn.constName!).type
  for arg in value.getAppArgs do
    let .forallE n _ tail _ := sig | throwError "unexpected geometry at {name}"
    if n == name then return arg
    sig := tail
  throwError "missing physical {name}"

/-- The sparse supplier records the original encoded pin in the positive
exterior that indexes its rows. -/
private def pinOfSuppliedSource (sparse : Expr) : MetaM Expr := do
  let sourceType ← inferType sparse
  let .forallE _ exterior _ _ ← whnf sourceType | throwError "expected the sparse exterior"
  let some domain ← whnfUntil exterior ``Subtype | throwError "expected the supported exterior coordinates"
  lambdaTelescope domain.getAppArgs.back! fun _ pred => do
    let some supported ← whnfUntil pred ``And | throwError "expected support of the positive exterior"
    let some positive ← whnfUntil supported.getAppArgs[0]! ``PositiveExterior |
      throwError "expected the positive original exterior"
    argumentNamed positive `pin

/-- Specialize the native continuation to the same recorded pin and sparse packet source. -/
private def nativeNextAtCheckedReports (calibrated : Array Expr) (sparse : Expr) : MetaM Expr := do
  let native ← mkConstWithLevelParams ``SignedCalendarAt.frozenNativeNext
  let count := (← getConstInfo ``SignedCalendarAt.frozenNativeNext).type.getForallArity
  let nativeAt := mkApp (mkAppN native (calibrated.extract 0 count)) (← pinOfSuppliedSource sparse)
  forallBoundedTelescope (← inferType nativeAt) (some 1) (whnfType:=true) fun measured _ => do
    mkLambdaFVars measured (mkApp (mkAppN nativeAt measured) sparse)

/-- At every checked operative calendar, calibrate the proper issued-report
reader on its own site packets and measured continuation. The field tuple,
team, display parameters and physical report remain arguments of the reader. -/
private def properMeasuredReportReader : MetaM Expr := do
  SignedCalendarAt.withCheckedRouteOperands ``SignedCalendarAt.routeInputsOnOriginalReports
    fun operative calibrated => do
      let issuer := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.suppliedOnOriginalReports) operative
      let observe := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.rosterOnIssuedReport) calibrated
      forallBoundedTelescope (← inferType issuer) (some 1) (whnfType:=true) fun packets _ => do
        let sparse := mkProj ``Prod 1 (mkAppN issuer packets)
        let native ← nativeNextAtCheckedReports calibrated sparse
        lambdaTelescope native fun measured next => do
          let onField := mkApp observe next
          forallBoundedTelescope (← inferType onField) (some 2) (whnfType:=true) fun fieldTeam _ => do
            let onReport := mkAppN onField fieldTeam
            forallTelescope (← inferType onReport) fun receipt _ => do
              mkLambdaFVars (packets ++ measured ++ fieldTeam ++ receipt) (mkAppN onReport receipt)

/-- Open exactly the five coordinates of the funded reporter's own field. The
last coordinate is the dependent report proposal, kept entire. -/
private partial def overOriginalField (domain : Expr) (names : List Name) (build : Expr → MetaM Expr) : MetaM Expr := do
  match names with
  | [] => throwError "empty original calendar field"
  | [n] => withLocalDeclD n domain fun q => do mkLambdaFVars #[q] (← build q)
  | name :: rest =>
    let d ← whnfHeadPred domain fun e => pure (!e.getAppFn.constName?.any (#[``Sigma,``PSigma,``Prod,``PProd].contains ·))
    let #[a,b] := d.getAppArgs | throwError "expected the original field pair, found {d.getAppFn.constName?}"
    let ctor ← match d.getAppFn.constName? with
      | some ``Sigma => pure ``Sigma.mk
      | some ``PSigma => pure ``PSigma.mk
      | some ``Prod => pure ``Prod.mk
      | some ``PProd => pure ``PProd.mk
      | _ => throwError "unexpected pair constructor at original field {name}"
    withLocalDeclD name a fun x => do
      let deeper := if ctor == ``Prod.mk || ctor == ``PProd.mk then b else b.beta #[x]
      let inside ← overOriginalField deeper rest fun tail =>
        build (mkApp4 (mkConst ctor d.getAppFn.constLevels!) a b x tail)
      mkLambdaFVars #[x] inside

/-- Recover the original route inputs from the calendar that supplies the stored
sites, retaining exactly the instances used by the route checker. -/
private def routeArguments (inputs : Array Expr) : MetaM (Array Expr) := do
  let mut sig := (← getConstInfo ``SignedCalendarAt.routeInputsOnOriginalReports).type
  let mut available := inputs
  let mut checked := #[]
  for _ in [:inputs.size] do
    let .forallE name wanted tail kind ← whnf sig | throwError "missing original report inputs"
    let some index ← available.findIdxM? (fun x => do
      if kind.isInstImplicit then
        let actual ← inferType x
        return actual == wanted || (← withReducible <| isDefEq actual wanted)
      return (← x.fvarId!.getUserName).eraseMacroScopes == name.eraseMacroScopes)
      | throwError "missing original route parameter {name}"
    let argument := available[index]!
    checked := checked.push argument
    if name.eraseMacroScopes == `reports then return checked
    sig := tail.instantiate1 argument
    available := available.eraseIdx! index
  throwError "missing the original report family"

private def throughStored (type : Expr) : MetaM Nat := do
  let mut sig := type
  let mut count := 0
  while sig.isForall do
    count := count + 1
    if sig.bindingName!.eraseMacroScopes == `stored then return count
    sig := sig.bindingBody!
  throwError "missing the family of stored original reports"

/-- Instantiate the directory and label parameters from the retained emission. -/
private def rosterOfStoredSite (read site : Expr) : MetaM Expr := do
  let original ← SignedCalendarAt.storedReportAtOriginalSite site
  let report := mkProj ``Subtype 0 original
  let some issued ← whnfUntil (← inferType report) ``EmittedReport |
    throwError "expected the stored emitted report"
  let mut signature := (← getConstInfo ``EmittedReport).type
  let mut labels := false
  let mut parameters := #[]
  for argument in issued.getAppArgs do
    let .forallE name _ tail _ := signature | throwError "unexpected emitted-report signature"
    if name == `E then labels := true
    if name == `dir || labels then parameters := parameters.push argument
    signature := tail
  let result := mkAppN read (parameters.push report)
  let prop ← inferType result
  return mkApp2 (mkConst ``PLift.up [← getLevel prop]) prop result

/-- Use the same stored site for both the supplied packets and the supported report. -/
private def registrationRoster (sites : Expr) : MetaM Expr := do
  let reader ← properMeasuredReportReader
  let args ← inferType sites
  forallBoundedTelescope args (some (← throughStored args)) (whnfType := true) fun all _ => do
    let stored := all.back!
    let packets := mkAppN sites all
    let atCut := (mkApp (mkAppN reader (← routeArguments all.pop)) packets).headBeta
    forallBoundedTelescope (← inferType atCut) (some 1) (whnfType := true) fun measured _ => do
      let atField := mkAppN atCut measured
      let .forallE _ fieldType _ _ ← whnf (← inferType atField) | throwError "missing the original field"
      let final ← overOriginalField fieldType [`raw,`hist,`route,`subtotal,`proposed] fun f => do
        let atTeam := mkApp atField f
        forallBoundedTelescope (← inferType atTeam) (some 1) (whnfType := true) fun team _ => do
          let site := mkApp2 stored f team[0]!
          mkLambdaFVars team (← rosterOfStoredSite (mkAppN atTeam team) site)
      mkLambdaFVars (all ++ measured) final

local elab "storedRegistrationRoster%" : term => do
  let sites ← mkConstWithLevelParams ``SignedCalendarAt.siteDataOnStoredReportsAtOriginalInputs
  let value ← registrationRoster sites
  let type ← inferType value
  let level ← getLevel type
  let domain := mkSort level
  let family := mkLambda `T .default domain (.bvar 0)
  return mkApp4 (mkConst ``PSigma.mk [level.succ, level]) domain family type value

private noncomputable def originalStoredRoster : (R : Sort _) ×' R := storedRegistrationRoster%

/-- At every original field and team, the report retained by the stored family
supplies the supported roster for the continuation measured on its own native sites. -/
noncomputable def SignedCalendarAt.rosterForRegistrationOnOriginalStoredReports :
    originalStoredRoster.1 := originalStoredRoster.2

end Diagonal

end BorderVNP
end Computability
end OAI
