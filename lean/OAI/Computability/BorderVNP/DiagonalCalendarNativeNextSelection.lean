import OAI.Computability.BorderVNP.DiagonalCalendarNativeNext

/-! # Agreement of the measured calendar and its selected sparse calls

The calendar returns a continuation for the selected pin, measured clock
and sparse input. Its selection theorem specializes the native call
identity to the exact operands of that calendar, including the returned
call whose private inputs are charged at the selected clock.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term TeamContraction.ProcessorSlots

/-- Apply the native selection identity to the particular call made by the
calendar, retaining the calendar selector itself on the left side. -/
private def measuredSourceAgreement : TermElabM (Expr × Expr) := do
  let cal ← mkConstWithLevelParams ``SignedCalendarAt.frozenNativeNext
  let info ← getConstInfo ``SignedCalendarAt.frozenNativeNext
  lambdaTelescope info.value! fun calendar _ => do
    let selection := mkAppN cal calendar
    forallBoundedTelescope (← inferType selection) (some 3) fun measured _ => do
      unless measured.size == 3 do throwError "expected the pin, measured clock, and sparse source"
      let actual := mkAppN selection measured
      let some call ← whnfUntil actual ``BootedPinStart.nativeNext |
        throwError "the frozen selector does not select a native measured call"
      -- The native identity has the same parameters as this native call.
      let read := mkAppN (← mkConstWithLevelParams ``BootedPinStart.nativeNext_eq) call.getAppArgs
      let equal ← inferType read
      let some (carrier, _, chosen) := equal.eq? | throwError "the native selector did not return an equality"
      let target := mkApp3 equal.getAppFn carrier actual chosen
      let parameters := calendar ++ measured
      return (← mkForallFVars parameters target, ← mkLambdaFVars parameters read)

open Elab.Command in
run_cmd liftTermElabM do
  let (statement, proof) ← measuredSourceAgreement
  -- Naming the complete proposition keeps its exported signature compact.
  let claim := `OAI.Computability.BorderVNP.Diagonal.SignedCalendarAt.MeasuredNativeNextSelection
  addDecl (.defnDecl {
    name := claim
    levelParams := []
    type := mkSort .zero
    value := statement
    hints := .abbrev
    safety := .safe })
  addDocStringCore claim "On each measured calendar pin the continuation is the family chosen by its sparse calls."
  let n := `OAI.Computability.BorderVNP.Diagonal.SignedCalendarAt.frozenNativeNext_selection
  addDecl (.thmDecl {name:=n, levelParams:=[], type:=mkConst claim, value:=proof})
  addDocStringCore n "The measured calendar continuation equals the original sparse continuation on every supported exterior and team."

end Diagonal

end BorderVNP
end Computability
end OAI
