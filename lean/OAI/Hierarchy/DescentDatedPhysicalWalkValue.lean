import OAI.Hierarchy.DescentDatedSampledOperandValues
import OAI.Hierarchy.DescentDatedBroadcastWalkNumber

namespace OAI
/-! # The measured inverse-ordinal column at the original dated receiver -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedOperandReadPipeline DescentDatedSourcePathDirectory DescentHaloWalkRAM
open DescentSharedCableNames DescentRawCablePanel DescentSIMDLookup
noncomputable section
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I)
set_option quotPrecheck false
local notation "e" => v.material
local notation "g" => v.ticketReadGeometry
local notation "fmt" => v.ticket.depotShape v.short
local notation "P" => breadth (fmt).degree

theorem sampled_walk_fits (p : Fin P) : p.val<2^v.operandShortBits :=by
  have cap : p.val<2^(Packed.bits P):=(Nat.lt_succ_of_le p.isLt.le).trans_le (Nat.le_pow_clog (by decide : 1<2) _)
  have bits : Packed.bits P≤v.operandShortBits:=by
    change Packed.bits P≤ max (max _ _) (max _ (Packed.bits P))
    exact (le_max_right _ _).trans (le_max_right _ _)
  exact cap.trans_le (Nat.pow_le_pow_right (by decide) bits)

theorem sampled_walk_number (R : Fin (e).oldHosts→Fin (fmt).degree→Option (Fin (e).oldHosts))
    (h : Fin (g).hosts) (y : Fin (g).groups) (recv u : Fin (e).oldHosts) (s p : Fin P)
    (atHost : DepotRAM.Material.Route.receiver (e).oldHosts v.materialPitch h=some recv)
    (sorted : DescentSortedRoster.indexed (Gather.reaching R) recv s=some u)
    (raw : Gather.select (Gather.reaching R) recv p=some u) :
    (v.walkValues (Gather.reaching R) s h y).val=Sorted.rawAtOrdinal (Gather.reaching R) recv s :=by
  exact SortedInput.Broadcast.value_at_ordinal g v.materialPitch (Gather.reaching R)
    h y recv u s p atHost sorted raw (v.sampled_walk_fits p)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
