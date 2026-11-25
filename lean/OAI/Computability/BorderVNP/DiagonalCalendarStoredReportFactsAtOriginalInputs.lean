import OAI.Computability.BorderVNP.DiagonalStoredOriginalFieldFacts
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalStoredCoordinateInputs
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalStoredMarkInputs
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalReportScan

/-! # Coordinates, layout and marks of a single funded original report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta RoutingISA.FragmentRows Packing.RoutingOutputs

set_option cleanup.letToHave false
set_option maxRecDepth 24000
set_option maxHeartbeats 16000000

private def equalitySides (type : Expr) : MetaM (Expr × Expr) := do
  let some (_, left, right) := (← whnfUntil type ``Eq).bind Expr.eq? |
    throwError "expected an equality of original report fields"
  return (left, right)

/-- The home of original bundle `j` is the physical cell of its original site.
Both maps occur in the same receiver used in the report's coordinate proof. -/
private def originalBundleHome (receiver : Expr) : MetaM Expr := do
  let some routing ← whnfUntil receiver ``NativeDemands.receiver |
    throwError "expected the issued delivery receiver"
  forallBoundedTelescope (← inferType routing.getAppFn) (some routing.getAppNumArgs) fun parameters _ => do
    let mut arguments : NameMap Expr := {}
    for parameter in parameters, value in routing.getAppArgs do
      arguments := arguments.insert (← getFVarLocalDecl parameter).userName.eraseMacroScopes value
    let some cell := arguments.find? `cell | throwError "missing the delivery cell map"
    let some original := arguments.find? `old | throwError "missing the original site embedding"
    let site ← mkProjection original `toFun
    forallBoundedTelescope (← inferType site) (some 1) fun index _ =>
      mkLambdaFVars index (mkApp cell (mkAppN site index))

/-- Specialize the native funding receipt at the coordinates read by the payer,
the retained payload read by the mark proof, and the independent chart equality. -/
private def originalReportFields (coordinates marks chart domain coordinateType report : Expr) : MetaM Expr :=
  withLocalDeclD `d domain fun d => do
    let fieldNames := #[`declaration, `label, `recv, `incoming]
    forallBoundedTelescope (coordinateType.instantiate1 d) (some fieldNames.size) fun fields coordinateGoal => do
      let mut saved := #[]
      for field in fields, name in fieldNames do
        let (reported, original) ← equalitySides (← inferType field)
        unless (← getFVarLocalDecl field).userName.eraseMacroScopes == name &&
            reported == (← mkProjection d name) do
          throwError "expected the original {name} equality on this report"
        saved := saved.push original
      unless saved.size == fieldNames.size do throwError "incomplete original report coordinates"
      let home ← originalBundleHome saved[2]!
      let (actualLayout, payerLayout) ← equalitySides (← inferType chart)
      let marked := mkApp marks d
      let .forallE bankName bankType bankRest binderInfo ← whnf (← inferType marked) |
        throwError "missing the retained report bank"
      unless bankName.eraseMacroScopes == `bank do throwError "expected the original report bank"
      withLocalDecl bankName binderInfo bankType fun bank => do
        let .forallE _ payloadEquality markGoal _ ← whnf (bankRest.instantiate1 bank) |
          throwError "missing the retained payload equality"
        let (reported, payload) ← equalitySides payloadEquality
        let ownPayload ← mkProjection d `payload
        let .ok true := Kernel.isDefEq (← getEnv) (← getLCtx)
            (ShareCommon.shareCommon reported) (ShareCommon.shareCommon ownPayload) |
          throwError "the mark proof reads a different report payload"
        if markGoal.hasLooseBVars then throwError "the mark bound depends on its equality witness"
        let coordinateClaim ← mkLambdaFVars #[d] coordinateGoal
        let markClaim ← mkLambdaFVars #[d] markGoal
        let atBank ← mkLambdaFVars #[d] (mkApp marked bank)
        let receipt := mkAppN (mkConst ``EmittedReport.payStoredOriginalFields [.param `nativeIndex])
          (report.getAppArgs ++ saved ++
            #[home, actualLayout, payerLayout, payload, coordinateClaim, markClaim, coordinates, atBank, chart])
        mkLambdaFVars #[bank] receipt

/-- Open the common calendar, field, team and inventory parameters of the two
payer obligations. The chart is indexed only through the team parameter. -/
private partial def onReportedField (coordinates marks layout type : Expr) (args : Array Expr) : MetaM Expr := do
  let reduced ← if type.isForall then pure type else whnf type
  let .forallE name domain body binderInfo := reduced |
    throwError "expected a funded report in the coordinate operation"
  if name.eraseMacroScopes == `d then
    if let some report ← whnfUntil domain ``EmittedReport then
      -- The four inventory binders are E, I, P and the enumeration of P.
      let throughTeam := args.extract 0 (args.size - 4)
      let some team := throughTeam.back? | throwError "missing the original team"
      unless (← getFVarLocalDecl team).userName.eraseMacroScopes == `u do
        throwError "expected the original team before the report inventory"
      let chart := mkAppN layout throughTeam
      let facts ← originalReportFields (mkAppN coordinates args) (mkAppN marks args) chart domain body report
      return ← mkLambdaFVars args facts
  withLocalDecl name binderInfo domain fun arg =>
    onReportedField coordinates marks layout (body.instantiate1 arg) (args.push arg)

open Lean.Elab.Term in
local elab "storedOriginalReportFacts%" : term => do
  let coordinates ← mkConstWithLevelParams ``SignedCalendarAt.paidCoordinatesAtOriginalInputs
  let marks ← mkConstWithLevelParams ``SignedCalendarAt.paidMarkBoundsAtOriginalInputs
  let layout ← mkConstWithLevelParams ``SignedCalendarAt.layoutAtOriginalReportedInputs
  onReportedField coordinates marks layout (← inferType coordinates) #[]

private def originalReportResult {P : Prop} (proof : P) : PSigma (fun statement : Prop => statement) :=
  ⟨P, proof⟩

private noncomputable def storedOriginalFields.{nativeIndex} : PSigma (fun statement : Prop => statement) :=
  originalReportResult storedOriginalReportFacts%

/-- On each original field and team, the same funded report supplies its four
payer coordinates, its chart layout and the mark bounds on all retained rows. -/
theorem SignedCalendarAt.storedReportFactsAtOriginalInputs.{nativeIndex} :
    storedOriginalFields.{nativeIndex}.1 := storedOriginalFields.2

end Diagonal

end BorderVNP
end Computability
end OAI
