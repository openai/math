import OAI.Computability.BorderVNP.DiagonalStoredOriginalSourceOperands

/-! # Storing the parameters of an original funded report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.SignedCalendarAt

open Lean Meta Elab Term

/-- Pack a single earned receipt at the field and team of the expected stored
family. The receipt itself is the last component, so its entire funding
predicate and the native call it issued remain attached to that report. -/
def packEarnedOriginalReportAt (receipt target : Expr) : MetaM Expr := do
  let (source, finitePort) ← storedOriginalInputs receipt
  let names := #[`E, `I, `P, `iP, `bank, `fit, `cells, `emission, `Seed, `seed, `native]
  let mut components : Array (Expr × Expr) := #[]
  let mut remaining := target
  for name in names do
    let some pair ← whnfUntil remaining ``PSigma
      | throwError "expected a dependent pair for the original report's {name}"
    let some value := (if name == `iP then some finitePort else source.find? name)
      | throwError "the funded report has no {name} parameter"
    components := components.push (pair, value)
    remaining := pair.appArg!.beta #[value]
  unless (← whnfUntil remaining ``Subtype).isSome do
    throwError "expected the complete original funded report after its source parameters"
  let mut packed := receipt
  for (pair, value) in components.reverse do
    packed := mkAppN (mkConst ``PSigma.mk pair.getAppFn.constLevels!) (pair.getAppArgs ++ #[value, packed])
  return packed

/-- Fill the expected original site from the single funding receipt which
carries its emission, retained bank, seed, and native call. -/
elab "packEarnedOriginalReportAt% " receipt:term:max : term <= target => do
  packEarnedOriginalReportAt (← elabTerm receipt none) target

end Diagonal.SignedCalendarAt

end BorderVNP
end Computability
end OAI
