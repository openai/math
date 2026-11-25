import OAI.Computability.BorderVNP.DiagonalOriginalCandidateVisitTerm
import OAI.Computability.BorderVNP.DiagonalCheckedReportOnRoute

/-! # Recovering the selected route's candidate on its original native visit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open RoutingISA.Evaluator TeamContraction

open Lean Meta Elab Term in
/-- Quantify the actual reported bank, digits and native visit at every original field. -/
elab (name := originalCandidateFamily) "originalCandidateFamily% " writers:term:max returnedSites:term:max
    admissions:term:max planner:term:max : term => do
  let native ← elabTerm writers none
  let lookup ← elabTerm returnedSites none
  let admitted ← elabTerm admissions none
  let task ← elabTerm planner none
  let .forallE _ fieldType _ _ ← whnf (← inferType native) |
    throwError "expected the native writer on each original calendar field"
  withLocalDeclD `f fieldType fun field => do
    let fields := mkProj ``Sigma 1 field
    let hist := mkProj ``Sigma 0 fields
    let entries := mkProj ``Sigma 1 fields
    let submitted := mkProj ``Subtype 0 (mkProj ``Sigma 0 entries)
    let claim := mkProj ``Prod 0 (mkProj ``Sigma 1 entries)
    let checked := mkApp3 lookup (mkProj ``Sigma 0 field) hist claim
    let honest := mkApp admitted hist
    let physical := mkProj ``And 0 (mkApp native field)
    let seen := mkProj ``And 0 physical
    let same := mkProj ``And 1 physical
    let t ← exprToSyntax task
    let route ← exprToSyntax submitted
    let raw ← elabTerm (← `(SignedPrep.routeBroadcast ($t).cube _ $route)) none
    synthesizeSyntheticMVarsNoPostponing
    let selected ← exprToSyntax (← instantiateMVars raw)
    let registered ← exprToSyntax checked
    let accepted ← exprToSyntax honest
    let witnessed ← exprToSyntax seen
    let attained ← exprToSyntax same
    let report ← elabTerm (← `(sourceCandidateAtVisit%
      (returnedReportOnRoute% $registered $selected $accepted $route) $witnessed $attained)) none
    let reportType ← inferType report
    let sameType ← inferType same
    let statement ← mkForallFVars #[field] (mkApp2 (mkConst ``And) reportType sameType)
    let both := mkAppN (mkConst ``And.intro) #[reportType,sameType,report,same]
    let certificate ← mkLambdaFVars #[field] both
    let propositions := mkSort .zero
    let identity := mkLambda `p .default propositions (.bvar 0)
    return mkAppN (mkConst ``PSigma.mk [.ofNat 1,.zero]) #[propositions,identity,statement,certificate]

end Diagonal

end BorderVNP
end Computability
end OAI
