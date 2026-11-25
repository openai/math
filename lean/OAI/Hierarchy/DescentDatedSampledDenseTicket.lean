import OAI.Hierarchy.DescentDatedPostedParentNumbers
import OAI.Hierarchy.DescentDatedSortedOperandAdapter
import OAI.Hierarchy.DescentDatedSampledWalkNumber
import OAI.Hierarchy.DescentDatedTicketNativePrivate

namespace OAI
/-! # A carried private pointer reads the dense old-host ordinal on the original matched panel -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentDatedSourcePathDirectory
open DescentHaloWalkRAM DescentSharedCableNames DescentPackedZip DescentSIMDLookup DescentRawCablePanel
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
local notation "e" => v.material
local notation "l" => v.resolver
local notation "g" => v.ticketReadGeometry
local notation "fmt" => v.ticket.depotShape v.short
local notation "P" => breadth (fmt).degree
variable (blocks : v.resolver.blocks=v.material.blocks) (bound : v.resolver.hosts≤v.material.hosts) (groups : v.resolver.groups=v.material.groups)
    (orig : Fin v.resolver.jobs→Fin 6→Values v.ticketReadGeometry v.operandShortBits)
    (prior : Fin v.resolver.jobs→Fin 4→Values v.ticketReadGeometry (v.resolver.size+2)) (birth : Fin v.resolver.jobs→Fin 3→Values v.ticketReadGeometry v.bornBook.bits)
    (wide : v.WideHead→Fin v.material.hosts→Fin v.material.groups→Cell v.material.fieldBits)
    (R : Fin v.material.oldHosts→Fin (v.ticket.depotShape v.short).degree→Option (Fin v.material.oldHosts))
local notation "heads" => v.sampleHeads blocks bound groups orig prior birth wide (v.narrowValue R)
local notation "raw" => v.originalValues heads
variable (recv old : Fin v.material.oldHosts) (p s : Fin (breadth (v.ticket.depotShape v.short).degree)) (h : Fin v.resolver.hosts) (y : Fin v.resolver.groups)
    (atHost : DepotRAM.Material.Route.receiver v.material.oldHosts v.materialPitch (h.castLE bound)=some recv)
    (walk : Gather.select (Gather.reaching R) recv p=some old)
    (ordinal : DescentSortedRoster.indexed (Gather.reaching R) recv s=some old)

include atHost walk ordinal in
theorem sampled_dense_rank : ((raw).rank p h y).val=s.val+1 :=by
  refine (v.original_rank_number heads p h y).trans ?_
  change ((DepotRAM.Material.Route.receiver (e).oldHosts v.materialPitch (h.castLE bound)).elim
    0 (fun z=>Local.token R z p)).val=s.val+1
  rw [atHost]
  exact Local.token_dense_at R recv old p s walk ordinal

local notation "inverse" => v.walkValues (Gather.reaching R)

include atHost walk ordinal in
/-- On an inherited private read the preserved W ordinal chooses the original walk,
and the live deduplicated endpoint gives its true dense ordinal back to the ticket. -/

theorem sampled_dense_private_ticket
    (j : Fin (l).jobs) (block : ℕ) (actor : ((raw).origin j 0 h y).val=1)
    (oldOrdinal : ((raw).origin j 1 h y).val=s.val) (oldBlock : ((raw).origin j 2 h y).val=block)
    (kind : ((raw).prior j 0 h y).val=0) :
    ticketAt g (SortedInput.values g raw inverse) j h y=![s.val*(fmt).blocks+block,0,0,0,0,0,0,0] :=by
  have input:=v.sampled_walk_number R h y recv old s p atHost ordinal walk
  have path : ((SortedInput.values g raw inverse).origin j 1 h y).val=p.val:=by
    change (SortedInput.selected g raw inverse j h y).val=p.val
    rw [SortedInput.selected_at g raw inverse j h y s (Or.inl actor) oldOrdinal,input,Sorted.raw_eq _ recv old s p ordinal walk]
  exact private_ticket g _ j h y p s.val block (by simpa [SortedInput.values] using actor) kind
    path (by simpa [SortedInput.values] using oldBlock)
    (v.sampled_dense_rank blocks bound groups orig prior birth wide R recv old p s h y atHost walk ordinal)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
