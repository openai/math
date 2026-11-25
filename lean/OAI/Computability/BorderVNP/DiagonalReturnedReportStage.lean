import OAI.Computability.BorderVNP.DiagonalFrozenReportKTerm

/-! # Report stages on the frame that supplied the candidate sites -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term

/-- Read a report stage at the original sites, frame, and inventory of a
supplied frozen report predicate. -/
elab "originalReportStage% " certificate:term:max stage:term:max : term => do
  let report ← elabTerm certificate (some (mkSort .zero))
  let stage ← elabTerm stage (some (Lean.mkConst ``TeamContraction.CandidateReportStage))
  let some original ← whnfUntil report ``SignedCalendarAt.frozenReportK |
    throwError "expected a frozen report predicate on the returned sites"
  let family := Lean.mkConst ``SignedCalendarAt.frozenReportTest original.getAppFn.constLevels!
  return mkApp (mkAppN family original.getAppArgs) stage

end Diagonal

end BorderVNP
end Computability
end OAI
