import OAI.Hierarchy.DescentDatedRegisteredTicketBoard

namespace OAI
/-! # The original physical ticket board resolves reset pointers with unused stored fields -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedPriorOperand DescentPackedZip DescentSIMDLookup DescentPackedColony
open DescentRawCablePanel DescentHaloWalkRAM DescentOperandStateBanks DescentOperandVectorArena
open DescentSharedCableNames DescentPriorOperandColumns DescentDatedOperandReadPipeline DescentDatedOperandCoordinates
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I) (floor w : ℕ) (cs : v.SignedChart)
    (A : v.ArgumentEntry) (mat : A.Match v floor) (shape : v.VectorShape)
local notation "l₀" => v.resolver
local notation "g₀" => v.ticketReadGeometry
local notation "end₀" => v.preparedUntil floor
local notation "vec₀" => v.vectorStart floor
local notation "route₀" => v.routedStart floor
local notation "C₀" => (A.directory v floor mat).refs
variable (blocks : v.resolver.blocks=v.material.blocks) (pg : Fin (7*v.vector.operands))
local notation "src₀" => v.nativeTicketExpr floor cs A mat shape blocks
local notation "prep₀" => v.nativeTicketPreparation floor w cs A mat shape blocks pg

theorem routed_native_ticket_tagged (m : Memory w) (books : Books (l₀)) (typed : BookTags books)
    (words : Fin (l₀).jobs → Fin (l₀).hosts → Fin (l₀).groups → Fin 8 → ℕ)
    (purchased : v.origin.preparationWords=v.originControlWords+v.originMouthWords+v.rootSourceSize)
    (admit : v.TicketAdmission floor w cs A mat pg)
    (space : v.endAddress floor<2^w) (wide : (l₀).lanes*DescentPackedOperand.unit (l₀).size≤w/2)
    (pages : ∀x p,Reads ((v.nativeArgs floor).previous x p) (books x p) (l₀).lanes (((C₀).phase w vec₀).image m))
    (held : ∀j f,Held (g₀) end₀ ((prep₀).image (((C₀).phase w vec₀).image m)) (src₀ j f)
      (fun h k=>(words j h k f:Cell ((l₀).size+2))))
    (flags : ∀j h k,Ticket.Flags (words j h k))
    (digits : ∀j h k,11*(v.ticketRoles words j 1 h k).val+(v.ticketRoles words j 2 h k).val<2^((l₀).size+2)) :
    let raw:=decodedBooks books (fun j h k=>DescentDatedPublicGrain.withGrain v.chosenGrain (v.ticketSides words j h k))
      (v.ticketRoles words) digits
    ∀j : Fin (l₀).jobs, Reads (Banks.wordBank (l₀) (v.normalizedEnd floor) j)
      (fun h k=>DescentPackedOperand.word ((raw j).compiled h k)) (l₀).lanes
      ((v.routedArguments floor (C₀) (src₀) (prep₀) shape space wide).image m) :=by
  obtain ⟨_,_,toOut,toKeys,last⟩:=v.routed_order floor
  have paid:=v.grain_after_sources floor purchased
  have cap : end₀<2^w:=by rw [←paid]; exact toOut.trans_lt (toKeys.trans_lt (last.trans_lt space))
  let input:=((C₀).phase w vec₀).image m
  have run:=v.ticket_preparation_any floor w cs A mat shape blocks pg admit cap input
  have lane : 0<(l₀).lanes:=by rw [shape.lanes]; exact admit.lanes
  exact v.routed_keys_of_sources_tagged floor (C₀) (src₀) (prep₀) shape space wide m books typed
    (v.ticketSides words) (v.ticketRoles words) digits lane pages
    (fun i hi=>run.1.frame i (.inl hi)) (fun j f=>by rw [paid]; exact run.2 j f)
    (v.ticket_target_sources words ((prep₀).image input) (src₀) end₀ held flags)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentPackedZip DescentSIMDLookup DescentPackedColony DescentRawCablePanel
open DescentHaloWalkRAM DescentSharedCableNames DescentDatedOperandReadPipeline DescentOperandVectorArena
open DescentDatedPriorOperand DescentOperandStateBanks DescentOrdinaryAtomFieldRAM DescentDatedOperandCoordinates
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I) (floor : ℕ) (c : v.SignedChart)
    (A : v.ArgumentEntry) (mat : A.Match v floor) (shape : v.VectorShape)
local notation "l₀" => v.resolver
local notation "e₀" => v.material
local notation "fmt₀" => v.ticket.depotShape v.short
local notation "g₀" => v.ticketReadGeometry
local notation "vx₀" => v.vector
local notation "bn₀" => v.bornBook
local notation "d" => v.operandShortBits
local notation "H" => (e₀).oldHosts
local notation "K" => (e₀).hosts
local notation "D" => (fmt₀).degree
local notation "P₀" => breadth D
local notation "G" => (e₀).groups
local notation "B" => (e₀).blocks
local notation "M" => (e₀).lanes
local notation "O" => DepotRAM.Material.roles fmt₀
local notation "val₀" => Fin K → Fin G → Cell (e₀).fieldBits
local notation "first₀" => v.donorEnd floor
local notation "start₀" => v.materialStart floor
local notation "limit₀" => (e₀).endAddress start₀
local notation "vec₀" => v.vectorStart floor
local notation "route₀" => v.routedStart floor
local notation "mouth₀" => v.originMouthEnd floor
local notation "head₀" => v.operandHeaderEnd floor
local notation "end₀" => v.preparedUntil floor
local notation "refs₀" => (A.directory v floor mat).refs
local notation "W₀" => (vx₀).lanes*(vx₀).radix
local notation "Val₀" => References.Rows (vx₀) v.reference.degree v.reference.k v.reference.oldNodes
  v.reference.capacity ((l₀).size+2)
local notation "reverse₀" => (v.operandRanks floor).reverseRank

variable (blocks : v.resolver.blocks=v.material.blocks) (bound : v.resolver.hosts≤v.material.hosts)
    (groups : v.resolver.groups=v.material.groups)
variable {w nb mb : ℕ} (pg : Fin v.vector.pageCount)
    (chip : Fin v.bornBook.hosts→Fin v.bornBook.groups→Cell v.bornBook.chipBits)
    (oldBooks : References.Rows v.vector v.reference.degree v.reference.k v.reference.oldNodes
      v.reference.capacity (v.resolver.size+2) nb mb)
    (home : v.bornBook.hosts=v.vector.hosts) (group : v.bornBook.groups=v.vector.groups*v.vector.radix)
    (word : v.bornBook.bits=v.resolver.size+2)
variable (R : Fin v.material.oldHosts → Fin (v.ticket.depotShape v.short).degree → Option (Fin v.material.oldHosts))
    (state : Fin v.material.oldHosts → Fin v.material.oldGroups → DepotRAM.Parts (v.ticket.depotShape v.short))
    (bands : v.material.oldGroups=v.material.groups*v.material.blocks)
    (serial peer : Fin v.material.blocks → Fin (breadth (v.ticket.depotShape v.short).degree*
      DepotRAM.Material.roles (v.ticket.depotShape v.short)) → Fin v.material.hosts → Fin v.material.groups → Cell v.material.fieldBits)
local notation "orig" => v.originHeaderValue shape (oldBooks pg)
local notation "lastRows" => v.headerMouthRows floor A mat oldBooks home group word
local notation "prior" => fun j f h k=>ScalarOperand.take (((l₀).index.symm j).2.1) (v.previousHeaderValue shape oldBooks j f h k)
local notation "born" => fun j f h k=>ScalarOperand.take (((l₀).index.symm j).2.1) (v.mouthHeaderValue floor A mat shape lastRows chip home group j f h k)
local notation "wide₀" => v.wideMaterialValues R state bands serial peer
local notation "jobData" => v.sampleHeads blocks bound groups orig prior born wide₀ (v.narrowValue R)
local notation "words" => ticketAt (g₀) (SortedInput.values (g₀) (v.originalValues jobData) (v.walkValues (Gather.reaching R)))
local notation "oldPages" => fun x p=>previousValues (l₀) (vx₀) shape.operands shape.blocks shape.hosts shape.groups
  (References.returnedValue (vx₀) oldBooks (l₀).nodes) p x
variable (adj parts : Bank) (initial m : Memory w)
local notation "head" => PriorHeader.image H G M D first₀ adj initial
local notation "gathered" => ((refs₀).phase w vec₀).image m
local notation "prefix" => (v.originAndMouth floor w A mat d ((refs₀) pg)).image gathered
local notation "here" => (v.operandEarlyPhase floor w A).image prefix
local notation "material₀" => (v.materialAt start₀ parts reverse₀ w).image head
local notation "src₀" => v.nativeTicketExpr floor c A mat shape blocks
local notation "prep₀" => v.nativeTicketPreparation floor w c A mat shape blocks pg

theorem registered_resolver_keys_tagged
    (cash : v.SignedRoom floor w) (admit : v.TicketAdmission floor w c A mat pg)
    (issued : PriorHeader.Room adj H G M D first₀ w) (bill : v.MaterialRoom start₀ parts reverse₀ w)
    (neighbor : ∀h j,initial (adj.base+h.val*D+j.val)=(number (R h j):Word w))
    (original : Reads parts (fun h g=>DepotRAM.combine fmt₀ (state h g)) (e₀).oldLanes initial)
    (partLow : parts.base+parts.size≤first₀)
    (saved : ∀a,a<limit₀→here a=material₀ a)
    (rosters : v.WalkBanks floor A (Gather.reaching R) (v.operandHeaderEnd floor) here)
    (parents : ∀x i,Source (v.parentSerial floor c x i) (serial x i) M here ∧ Source (v.parentPeer floor c x i) (peer x i) M here)
    (grown : 0<(e₀).oldLanes)
    (panel : Reads A.venue.panel (fun h g=>DepotRAM.combine fmt₀ (state h g)) (e₀).oldLanes m)
    (early : A.venue.panel.base+A.venue.panel.size≤vec₀)
    (good : (refs₀).Room w vec₀) (input : (A.chipBank v floor).Fits w vec₀) (span : (bn₀).rows≤(A.chipBank v floor).size)
    (data : Reads (A.chipBank v floor) chip (bn₀).lanes m)
    (lane : (bn₀).lanes=W₀) (wideBook : (vx₀).bookBits=((l₀).size+2)*(l₀).nodes)
    (pages : ∀p q,ScalarOperand.Measured ((refs₀) p q) (oldBooks p q) (l₀).nodes W₀ vec₀ m)
    (purchased : v.origin.preparationWords=v.originControlWords+v.originMouthWords+v.rootSourceSize)
    (full : v.endAddress floor<2^w) (wide : (l₀).lanes*DescentPackedOperand.unit (l₀).size≤w/2)
    (typed : BookTags oldPages) (cap : 22*(fmt₀).cap+10<2^((l₀).size+2))
    :
    let digits:=fun j h k=>v.matched_role_room R state bands serial peer blocks bound groups orig prior born j h k
      (v.raw_role_room floor A mat shape pg oldBooks chip home group word m (Nat.mul_pos admit.lanes admit.radix) pages j h k) cap
    let raw:=decodedBooks oldPages
      (fun j h k=>DescentDatedPublicGrain.withGrain v.chosenGrain (v.ticketSides words j h k)) (v.ticketRoles words) digits
    ∀j : Fin (l₀).jobs, Reads (Banks.wordBank (l₀) (v.normalizedEnd floor) j)
      (fun h k=>DescentPackedOperand.word ((raw j).compiled h k)) (l₀).lanes
      ((v.routedArguments floor (refs₀) (src₀) (prep₀) shape full wide).image m) :=by
  intro digits raw
  have paid:=v.grain_after_sources floor purchased
  have order:=v.routed_order floor
  have room : end₀<2^w:=by
    rw [←paid]
    exact order.2.2.1.trans_lt (order.2.2.2.1.trans_lt (order.2.2.2.2.trans_lt full))
  have reads:=v.registered_ticket_board floor c A mat shape blocks bound groups pg chip oldBooks home group word
    R state bands serial peer adj parts initial m cash admit issued bill neighbor original partLow saved rosters parents grown
    panel early good input span data lane wideBook pages room
  exact v.routed_native_ticket_tagged floor w c A mat shape blocks pg m oldPages typed words purchased admit full wide
    reads.2 reads.1 (v.matched_ticket_flags R state bands serial peer blocks bound groups orig prior born) digits

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
