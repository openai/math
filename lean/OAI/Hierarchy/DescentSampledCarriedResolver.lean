import OAI.Hierarchy.DescentDatedDecodedSourceKey
import OAI.Hierarchy.DescentIssuedOperandKey
import OAI.Hierarchy.DescentDatedSampledDenseTicket
import OAI.Hierarchy.DescentDatedSortedBroadcast

namespace OAI
/-! The dense source ordinate and old private alias read by the concrete resolver job. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentDatedSourcePathDirectory
open DescentHaloWalkRAM DescentSharedCableNames DescentPackedZip DescentSIMDLookup DescentRawCablePanel
open DescentDatedPriorOperand DescentOperandStateBanks DescentPackedOperand DescentDatedOperandCoordinates
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

variable (inverse:Fin (breadth (v.ticket.depotShape v.short).degree)→Values v.ticketReadGeometry v.operandShortBits)
local notation "words" => ticketAt g (SortedInput.values g raw inverse)
variable (earlier:Books v.resolver) (typed:BookPointers earlier)
include atHost walk ordinal in
theorem sampled_carried_resolver
  (room:∀i a b,11*(v.ticketRoles words i 1 a b).val+(v.ticketRoles words i 2 a b).val<2^((l).size+2))
    (j:Fin (l).jobs) (block «alias»:ℕ)
    (actor:((raw).origin j 0 h y).val=1) (oldOrdinal:((raw).origin j 1 h y).val=s.val)
    (oldBlock:((raw).origin j 2 h y).val=block)
    (priorAt:((raw).prior j 0 h y).val=(booksHeader earlier j h y 0).val)
    (pointer:∀f,(booksHeader earlier j h y f).val=(Pointer.privateWord «alias»).header f)
    (path:(inverse s h y).val=Sorted.rawAtOrdinal (Gather.reaching R) recv s)
    (fits:s.val*(fmt).blocks+block<2^((l).size+2)) :
    resolve ((ofBooks earlier typed
      (fun i a b=>DescentDatedPublicGrain.withGrain v.chosenGrain (v.ticketSides words i a b))
      (v.ticketRoles words) room j).compiled h y)=Key.carried (s.val*(fmt).blocks+block) «alias» :=by
  have selected : ((SortedInput.values g raw inverse).origin j 1 h y).val=p.val := by
    change (SortedInput.selected g raw inverse j h y).val=p.val
    rw [SortedInput.selected_at g raw inverse j h y s (Or.inl actor) oldOrdinal, path,
      Sorted.raw_eq _ recv old s p ordinal walk]
  have measured := private_ticket g (SortedInput.values g raw inverse) j h y p s.val block
    (by simpa [SortedInput.values] using actor) (priorAt.trans (pointer 0)) selected
    (by simpa [SortedInput.values] using oldBlock)
    (v.sampled_dense_rank blocks bound groups orig prior birth wide R recv old p s h y atHost walk ordinal)
  exact source_carried l earlier typed words v.chosenGrain room j h y «alias» _ pointer
    (congrFun measured 0) fits

local notation "inv" => v.walkValues (Gather.reaching R)
local notation "registered" => ticketAt g (SortedInput.values g raw inv)

include atHost walk ordinal in
theorem registered_carried_resolver_decoded (previous:Books l)
    (lim:∀i a b,11*(v.ticketRoles registered i 1 a b).val+(v.ticketRoles registered i 2 a b).val<2^((l).size+2))
    (j:Fin (l).jobs) (block «alias»:ℕ) (actor:((raw).origin j 0 h y).val=1)
    (previousOrdinal:((raw).origin j 1 h y).val=s.val) (oldBlock:((raw).origin j 2 h y).val=block)
    (priorAt:((raw).prior j 0 h y).val=(booksHeader previous j h y 0).val)
    (pointer:∀f,(booksHeader previous j h y f).val=(Pointer.privateWord «alias»).header f)
    (fits:s.val*(fmt).blocks+block<2^((l).size+2)) :
    let jobs:=decodedBooks previous
      (fun i a b=>DescentDatedPublicGrain.withGrain v.chosenGrain (v.ticketSides registered i a b))
      (v.ticketRoles registered) lim
    resolve ((jobs j).compiled h y)=Key.carried (s.val*(fmt).blocks+block) «alias» :=by
  intro jobs
  have measured:=v.sampled_dense_private_ticket blocks bound groups orig prior birth wide R recv old p s h y
    atHost walk ordinal j block actor previousOrdinal oldBlock (priorAt.trans (pointer 0))
  exact source_carried_decoded l previous registered v.chosenGrain lim j h y «alias» _
    (pointer 0) (pointer 2) (congrFun measured 0) fits

include atHost walk ordinal in
theorem registered_carried_resolver (previous:Books l) (readback:BookPointers previous)
    (lim:∀i a b,11*(v.ticketRoles registered i 1 a b).val+(v.ticketRoles registered i 2 a b).val<2^((l).size+2))
    (j:Fin (l).jobs) (block «alias»:ℕ) (actor:((raw).origin j 0 h y).val=1)
    (previousOrdinal:((raw).origin j 1 h y).val=s.val) (oldBlock:((raw).origin j 2 h y).val=block)
    (priorAt:((raw).prior j 0 h y).val=(booksHeader previous j h y 0).val)
    (pointer:∀f,(booksHeader previous j h y f).val=(Pointer.privateWord «alias»).header f)
    (fits:s.val*(fmt).blocks+block<2^((l).size+2)) :
    let jobs:=ofBooks previous readback
      (fun i a b=>DescentDatedPublicGrain.withGrain v.chosenGrain (v.ticketSides registered i a b))
      (v.ticketRoles registered) lim
    resolve ((jobs j).compiled h y)=Key.carried (s.val*(fmt).blocks+block) «alias» :=by
  exact v.registered_carried_resolver_decoded blocks bound groups orig prior birth wide R recv old p s h y
    atHost walk ordinal previous lim j block «alias» actor previousOrdinal oldBlock priorAt pointer fits

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
