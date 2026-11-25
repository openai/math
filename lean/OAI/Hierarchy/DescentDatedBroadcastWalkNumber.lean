import OAI.Hierarchy.DescentDatedSortedBroadcast

namespace OAI
/-! # The raw walk chosen by the broadcast for an occupied sorted host slot -/
namespace Hierarchy.DescentDatedOperandReadPipeline.SortedInput.Broadcast
open DescentDatedSourcePathDirectory DescentSortedRoster DescentHaloWalkRAM DescentRawCablePanel
noncomputable section
variable (g : Geometry) {H : ℕ}

/-- Read one lane of the actual truncated broadcast. Repeated visits to the
same donor are resolved by the selector on the original walk list. -/
theorem value_at_ordinal (pitch : ℕ) (reach : Fin H → Fin g.paths → Option (Fin H))
    (h : Fin g.hosts) (y : Fin g.groups) (recv donor : Fin H) (s p : Fin g.paths)
    (atHost : DepotRAM.Material.Route.receiver H pitch h = some recv)
    (sorted : indexed reach recv s = some donor) (visited : Gather.select reach recv p = some donor)
    (room : p.val < 2^g.digitBits) :
    (value g pitch reach s h y).val = Sorted.rawAtOrdinal reach recv s := by
  simp only [value, atHost, Option.elim_some, Sorted.raw_eq reach recv donor s p sorted visited]
  exact Nat.mod_eq_of_lt room

theorem selected_at_ordinal (data : Data g) (pitch : ℕ) (reach : Fin H → Fin g.paths → Option (Fin H))
    (j : Fin g.jobs) (h : Fin g.hosts) (y : Fin g.groups) (recv donor : Fin H) (s p : Fin g.paths)
    (actor : (data.origin j 0 h y).val=1 ∨ (data.origin j 0 h y).val=2)
    (stamped : (data.origin j 1 h y).val=s.val)
    (atHost : DepotRAM.Material.Route.receiver H pitch h = some recv)
    (sorted : indexed reach recv s = some donor) (visited : Gather.select reach recv p = some donor)
    (room : p.val < 2^g.digitBits) :
    ((SortedInput.values g data (value g pitch reach)).origin j 1 h y).val=p.val := by
  change (SortedInput.selected g data (value g pitch reach) j h y).val=p.val
  rw [SortedInput.selected_at g data (value g pitch reach) j h y s actor stamped,
    value_at_ordinal g pitch reach h y recv donor s p atHost sorted visited room,
    Sorted.raw_eq reach recv donor s p sorted visited]

end
end Hierarchy.DescentDatedOperandReadPipeline.SortedInput.Broadcast

end OAI
