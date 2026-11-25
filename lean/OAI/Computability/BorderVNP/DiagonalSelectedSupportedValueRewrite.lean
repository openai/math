import OAI.Computability.BorderVNP.DiagonalSelectedSupportedValues
import Mathlib.Tactic.Conv

/-! # Rewriting the selected preparation without rebuilding its routed argument -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Lean Meta Elab Tactic

/-- Apply `signedSupportedIssuedPrefixes_val` to the arguments already present in
the native preparation. In particular the elaborator need not infer the type of
the physical routed equivalence again at a fully instantiated calendar. -/
elab (name := issuedPreparationValue) "issued_preparation_value" : conv => withMainContext do
  let lhs ← withReducible <| whnf (← Conv.getLhs)
  let native ← match lhs.consumeMData with
    | .proj ``Subtype 0 value => pure value
    | e =>
      unless e.getAppFn.isConstOf ``Subtype.val do
        throwError "expected the value of a selected preparation"
      pure e.appArg!
  let native ← withReducible <| whnf native
  let .const name levels := native.getAppFn | throwError "expected a native preparation application"
  unless name == ``signedSupportedIssuedPrefixes do
    throwError "expected signedSupportedIssuedPrefixes, found {name}"
  let proof := mkAppN (mkConst ``signedSupportedIssuedPrefixes_val levels) native.getAppArgs
  let some (_, _, rhs) ← matchEq? (← inferType proof) | throwError "expected a preparation equality"
  Conv.updateLhs rhs proof

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
