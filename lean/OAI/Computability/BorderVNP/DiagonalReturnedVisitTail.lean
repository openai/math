import OAI.Computability.BorderVNP.DiagonalOwnedReportReconstruction

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # The three actual terminal visits of a fully reconstructed report execution -/

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally DiagonalTallyCellReports

variable {w dim b h K s : ℕ} (id : TableEntry dim b h K s → ℕ)
    {World Team : Type*} (pub : World → Team → Arg → Word w)
    (mac : World → Team → TeamOpcode.Macros w 8) (reg : World → Team → Bank w) (mem : World → Team → Memory w)

set_option maxHeartbeats 500000 in
/-- A joint preparation matching the actual scheduled replay has the three
same terminal cuts as its owned scanner on each receiving team. Equality of
the entire report proposal includes all proposed digits, before any test of
the private cells. The three returned values live in homogeneous types even
when the start states of their dependent paths differ. -/
theorem returned_report_visits (world : World)
    (scheduleAt : ∀ u, Returns (schedule dim K h) (pub world u) (mac world u) (reg world u) (mem world u))
    (empty : ∀ u, (scheduleAt u).val.1.flatMap TeamRAM.Event.choices=[])
    (routed : ∀ u, Returns route (pub world u) (mac world u) (scheduleAt u).val.2.1 (scheduleAt u).val.2.2)
    (inputs : ∀ u, Returns (signedInputs id (TeamRows.ownedGroups dim b h K s)) (pub world u) (mac world u)
      (routed u).val.2.1 (routed u).val.2.2)
    (full : Σ x : World, ∀ u : Team, Returns
      (prepareExpansion epochPlacement (scheduleGroups dim (selectorWidth dim K h))
        (signedInputs id (TeamRows.ownedGroups dim b h K s)))
      (pub x u) (mac x u) (reg x u) (mem x u))
    (whole : full=⟨world,fun u => (fixedScheduleEquiv id (scheduleAt u) (empty u)) ⟨routed u,inputs u⟩⟩) (u : Team)
    (constant : Returns (CubeConstants.install id) (pub world u) (mac world u) (routed u).val.2.1 (routed u).val.2.2)
    (owned : Returns (TeamRows.ownedGroups dim b h K s) (pub world u) (mac world u) constant.val.2.1 constant.val.2.2)
    (ctl : Returns controls (pub world u) (mac world u) owned.val.2.1 owned.val.2.2)
    (data : LocalReportData (pub world u) (mac world u) owned.val.2.1 owned.val.2.2)
    (bits : ReportAssignments data.cells)
    (localInput : inputs u=(inputCut id (pub world u) (mac world u) constant).symm
      ⟨owned,(fittedReportTailEquiv ctl (data.seed ctl) (data.argumentsFit ctl)).symm bits⟩) :
    let v := (visitsEquiv id (pub full.1 u) (mac full.1 u) (reg full.1 u) (mem full.1 u)).symm (full.2 u)
    let r := assignedReportReturnEquiv (data.seed ctl) (mac full.1 u) ctl.val.2.1 bits
    let a := (arguments_returns (data.argumentsFit ctl bits)).some
    (v.controls.val,v.reports.val,v.arguments.val)=(ctl.val,r.val,a.val) := by
  subst full
  dsimp only
  rw [localInput]
  exact visits_rebuilt_tail id (scheduleAt u) (empty u) (routed u) constant owned ctl data bits

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
