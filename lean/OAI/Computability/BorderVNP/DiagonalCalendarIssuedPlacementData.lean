import OAI.Computability.BorderVNP.DiagonalCalendarIssuedEvidence

/-! # Native issuing evidence with the calendar's actual saved placement -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta

local elab "calendarHeldIssuanceType%" : term => do inferType (← originalIssuanceTerm true)

/-- The native operation with the attained rectangle and its returned sparse-field array retained. -/
noncomputable abbrev SignedCalendarAt.FrozenHeldIssuance : Type _ := calendarHeldIssuanceType%

/-- Every reported field is checked on the same original candidate and the
real acquired source whose physical placement the calendar retained. -/
noncomputable def SignedCalendarAt.frozenIssuedReadbackOfCandidates : SignedCalendarAt.FrozenHeldIssuance := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← originalIssuanceTerm true)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
