import OAI.Computability.BorderVNP.PackedHistorySubdivisionPointers
import OAI.Computability.BorderVNP.PackedInheritedLayerInputs
import OAI.Computability.BorderVNP.PackedSubdivisionSlices

/-! # Static public slots for endpoint and relay records in the subdivision -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision.Gates

open CellAddressCircuit PackedHistoryCircuit.RouteRows

/-- Old cable rows interleave the two endpoint candidates; exterior ports follow. -/
abbrev Old (m np : ℕ) := (Fin m × Bool) ⊕ Fin np

/-- The old endpoint candidates followed by the fixed interior relay rectangle. -/
abbrev Row (m np extra : ℕ) := Old m np ⊕ (Fin m × Fin extra)

/-- Old physical end selected by a raw candidate. -/
def oldEnd {m np : ℕ} : Old m np → End m np
  | .inl (e,side) => Layer.edgeEnd e side
  | .inr p => .inr p

/-- Stripe ID of an individual new hop, before checking row occupancy. -/
def hop {m extra : ℕ} (e : Fin m) (j : Fin (extra+1)) : Fin ((extra+1)*m) := edgeIndex m extra (e,j)

/-- Endpoint of the first or last reserved hop. The public last-hop flag selects
the long route, or hop zero for a cable with no inserted relay. -/
def oldTarget {m np extra : ℕ} (r : Old m np) (long : Bool) : End ((extra+1)*m) np :=
  match r with
  | .inr p => .inr p
  | .inl (e,side) => Layer.edgeEnd (hop e (if side then 0 else if long then Fin.last extra else 0)) side

/-- The predecessor word ends at the relay. -/
def relayLeft {m np extra : ℕ} (e : Fin m) (j : Fin extra) : End ((extra+1)*m) np :=
  Layer.edgeEnd (hop e j.castSucc) false

/-- The successor word starts at the same relay. -/
def relayRight {m np extra : ℕ} (e : Fin m) (j : Fin extra) : End ((extra+1)*m) np :=
  Layer.edgeEnd (hop e j.succ) true

end Packing.Inherited.Subdivision.Gates

end BorderVNP
end Computability
end OAI
