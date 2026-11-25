import OAI.Computability.BorderVNP.DiagonalCalendarRoutedPostClock
import OAI.Computability.BorderVNP.DiagonalIssuedHeaderPostFamily

/-! # The full original issued post family at the calibrated phase clock -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta TeamContraction.ProcessorSlots RoutingISA.Evaluator.ScheduleClock

private def operandsOf (body : Expr) : MetaM (Array (Name × Expr)) := do
  let some name := body.getAppFn.constName? | throwError "expected a physical post at the calibrated field"
  let mut signature := (← getConstInfo name).type
  let mut values := #[]
  for x in body.getAppArgs do
    values := values.push (signature.bindingName!,x)
    signature := signature.bindingBody!
  return values

private def postOperand (values : Array (Name × Expr)) (n : Name) : MetaM Expr := do
  let some (_,x) := values.find? (fun p => p.1==n) | throwError "missing native post operand {n}"
  return x

/-- Return the original phase record of the measured argument/call budget. -/
private def originalCharges (budget : Expr) : MetaM Expr := do
  unless budget.isAppOfArity ``PhaseCharges.argumentsCalls 1 do
    throwError "expected the argument/call field of the calibrated phase clock"
  return budget.appArg!

/-- Use the physical clock read from the actual calibrated writer to specialize
the generic all-fields post theorem. It takes the identical phases, model,
startup, dimensions and reader clocks that appear in the literal post. -/
private def nominalPostMap : MetaM Expr := do
  let .defnInfo issuing ← getConstInfo ``SignedCalendarAt.FrozenIssuingRoutes
    | throwError "expected the native issuing routes"
  let .defnInfo check ← getConstInfo ``SignedCalendarAt.RoutedPostClock
    | throwError "expected the calibrated scalar clock map"
  forallBoundedTelescope check.value (some (issuing.value.getForallArity+1)) fun params implication => do
    let inputs := (params.extract 0 (params.size-2)).push params.back!
    let native ← instantiateForall issuing.value inputs
    let some roster ← whnfUntil native ``BootedPinStart.PreparedHistoryDecoder.RosterRoutes
      | throwError "expected the original native source roster"
    let routed := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuingRoutes) inputs
    let mapper := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.issuedClockOfPostRequests) params
    let .forallE _ charged observed _ ← whnf implication | throwError "expected the native scalar implication"
    unless !observed.hasLooseBVar 0 do throwError "post data cannot depend on its evidence"
    let some outcome ← whnfUntil (observed.instantiate1 (mkConst ``True.intro))
        ``BootedPinStart.PreparedHistoryDecoder.HeaderAssertions
      | throwError "expected the assertion on the original native header"
    let predicate := outcome.getAppArgs.back!
    let typed ← forallBoundedTelescope (← inferType predicate) (some 5) fun fields _ => do
      let some exec ← whnfUntil (mkAppN predicate fields) ``RoutingISA.Evaluator.PinStart.ChargedPost
        | throwError "expected the scalar clock of the native writer"
      let values ← operandsOf exec
      let task ← postOperand values `task
      let startup ← postOperand values `A
      let cost ← originalCharges (← postOperand values `budget)
      let scalars ← #[`entryWords,`indexBits,`dim,`subt,`P,`L,`F,`H].mapM (postOperand values)
      return mkAppN (← mkConstWithLevelParams ``BootedPinStart.PreparedHistoryDecoder.allPostsOfHeaderAssertions)
        (roster.getAppArgs ++ #[routed,task,startup,cost] ++ scalars)
    withLocalDeclD `post charged fun h =>
      mkLambdaFVars (params.push h) (mkApp typed (mkApp mapper h))

local elab "nativePostClockFamily%" : term => do inferType (← nominalPostMap)

/-- The original writer charges imply the full native post family on this same calibrated roster. -/
abbrev SignedCalendarAt.NominalIssuedPostMap : Prop := nativePostClockFamily%

/-- Every native phase and the whole-field post receipt use the one recovered
writer source and the previously calibrated phase record. -/
theorem SignedCalendarAt.allIssuedPostsOfRequests : SignedCalendarAt.NominalIssuedPostMap := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← nominalPostMap)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
