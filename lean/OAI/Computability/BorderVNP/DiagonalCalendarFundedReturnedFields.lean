import OAI.Computability.BorderVNP.DiagonalCalendarBareReportAssignments
import OAI.Computability.BorderVNP.DiagonalCalendarMarkedAssignedReportFields

/-! # Funded sparse fields of the original calendar report -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

namespace Diagonal
open Lean Meta
open VPVNP.BurstRAM TeamContraction.ProcessorSlots RoutingISA Evaluator SignedPrep DiagonalTallyCellReports

private def atHead (e : Expr) (n : Name) : MetaM Expr := do
  if e.isAppOf n then return e
  let some result ← whnfUntil e n | throwError "expected {n} while reading the returned native chart"
  return result

private def namedOperands (e : Expr) : MetaM (Array (Name × Expr)) := do
  let some n := e.getAppFn.constName? | throwError "expected a declared operand type"
  let mut t := (← getConstInfo n).type
  let mut fields := #[]
  for a in e.getAppArgs do
    fields := fields.push (t.bindingName!, a)
    t := t.bindingBody!.instantiate1 a
  return fields

private def fetch (fields : Array (Name × Expr)) (n : Name) : MetaM Expr := do
  let some x := fields.toList.lookup n | throwError "missing operand {n}; have {fields.map Prod.fst}"
  return x

private def pairAt (p : Expr) (i : Nat) : MetaM Expr := do
  let t ← whnf (← inferType p)
  let some n := t.getAppFn.constName? | throwError "expected a field pair"
  return mkProj n i p

/-- Use the original returned report, its true initial native state and its exact
report cursor from the chosen cut to fill the tested numerical compiler. -/
private def makeReturnedFields : MetaM Expr := do
  let .defnInfo raw ← getConstInfo ``SignedCalendarAt.frozenBareReportAssignments
    | throwError "expected the registered original report"
  lambdaTelescope raw.value fun xs _ => do
    let registry := mkAppN (← mkConstWithLevelParams raw.name) xs
    let some valueAt ← xs.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `values)
      | throwError "missing original source matrices"
    let values := xs[valueAt]!
    let static := xs.extract 0 valueAt
    let start := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenMarkedAssignedReportFields) static
    let first ← whnf (← inferType start)
    unless first.isForall && first.bindingName! == `funding do
      throwError "registered and funded calendar telescope disagree at {first.bindingName!}"
    let shape ← atHead (← inferType registry) ``BootedPinStart.BareAssignmentReturns
    let G ← fetch (← namedOperands shape) `G
    withLocalDeclD `funding first.bindingDomain! fun funding => do
      let family := mkProj ``PLift 0 registry
      forallBoundedTelescope (← inferType family) (some 2) fun fu _ => do
        let f := fu[0]!
        let u := fu[1]!
        let idx ← pairAt f 0
        let histField ← pairAt f 1
        let hist ← pairAt histField 0
        let routeField ← pairAt histField 1
        let rt ← pairAt routeField 0
        let proposed ← pairAt routeField 1
        let assignments ← pairAt proposed 1
        let present := mkAppN family fu
        let withDescription ← mkAppM ``Exists.choose_spec #[present]
        let receipt ← mkAppM ``Exists.choose_spec #[withDescription]
        let chosen ← mkAppM ``Classical.choice #[receipt]
        let exactArgs ← namedOperands (← atHead (← inferType chosen) ``ReportArgumentCut)
        let native := mkAppN start #[funding, values, hist, rt, u, assignments,
          ← fetch exactArgs `pub, ← fetch exactArgs `mac, ← fetch exactArgs `t,
          ← fetch exactArgs `v, ← fetch exactArgs `actual]
        let next ← whnf (← inferType native)
        unless next.isForall && next.bindingName! == `banks do
          throwError "expected the physical bank layout after the actual returned report"
        withLocalDeclD `banks next.bindingDomain! fun banks => do
          let pins ← mkAppM ``ExternalSew.freeBits #[G,idx]
          let paid := mkAppN native #[banks, ← fetch exactArgs `q,
            ← fetch exactArgs `description, chosen, pins]
          forallBoundedTelescope (← inferType paid) (some 2) fun binds _ => do
            unless binds.size == 2 do throwError "expected the marker memory and its evidence"
            let fields := mkProj ``PLift 0 (mkAppN paid binds)
            let cells ← mkLambdaFVars (fu ++ #[banks] ++ binds) fields
            let held ← mkAppM ``PLift.up #[cells]
            mkLambdaFVars (static ++ #[funding] ++ xs.extract valueAt xs.size) held

set_option maxRecDepth 14000
set_option maxHeartbeats 6000000
local elab "originalFundedFieldsType%" : term => do inferType (← makeReturnedFields)

/-- The sparse field readout on every original report, at its actual report cursor. -/
noncomputable abbrev SignedCalendarAt.OriginalFundedFieldsType : Type _ := originalFundedFieldsType%

/-- Use the actual original route and sampled report of each field and team to instantiate
the marked sparse compiler with its exact count and use data. -/
noncomputable def SignedCalendarAt.fundedReturnedFieldsAt : SignedCalendarAt.OriginalFundedFieldsType := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← makeReturnedFields)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
