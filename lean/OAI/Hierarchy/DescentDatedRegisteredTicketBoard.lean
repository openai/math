import OAI.Hierarchy.DescentDatedNativeTicketHeadRoom
import OAI.Hierarchy.DescentDatedRetainedMaterialBoards
import OAI.Hierarchy.DescentDatedSampledBirthRole
import OAI.Hierarchy.DescentDatedRegisteredHeaders
import OAI.Hierarchy.DescentDatedMatchedRoutedArguments
import OAI.Hierarchy.DescentDatedTicketRoleRoom

namespace OAI
/-! # Reading the actual ordinary scalar resolver from its registered operand pages -/
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

theorem registered_ticket_board
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
    (room : end₀<2^w) :
    (∀j f,Held (g₀) end₀ ((prep₀).image gathered) (src₀ j f) (fun h k=>(words j h k f:Cell (g₀).resultBits))) ∧
      ∀x p,Reads ((v.nativeArgs floor).previous x p) (oldPages x p) (l₀).lanes gathered :=by
  obtain ⟨r₁,r₂,r₃,r₄,r₅,r₆,r₇,r₈,r₉⟩:=v.ticket_source_order floor
  have headRoom:=(r₇.trans (r₈.trans r₉)).trans_lt room
  have firstRoom:=r₄.trans_lt (r₅.trans_lt (r₆.trans_lt headRoom))
  have gather:=(refs₀).any vec₀ m good
  have origin:=v.originPrefix_run floor d w ((refs₀) pg) gathered admit.mask (r₃.trans_lt firstRoom)
  have moved:=v.originPrefixMouth_any floor A mat ((v.originPrefix floor d w ((refs₀) pg)).image gathered) admit.chip admit.groups admit.lanes admit.radix admit.refs firstRoom
  have oldPanel : Reads A.venue.panel (fun h g=>DepotRAM.combine fmt₀ (state h g)) (e₀).oldLanes prefix:=by
    intro j
    have lo : A.venue.panel.base+(row H (e₀).oldGroups (e₀).oldLanes j).val<vec₀:=
      (Nat.add_lt_add_left ((row H (e₀).oldGroups (e₀).oldLanes j).isLt.trans_le admit.capacity) _).trans_le early
    have mid:=lo.trans_le (v.vector_before floor)
    exact (moved.2 _ (.inl (mid.trans_le (r₁.trans r₂)))).trans
      ((origin.2 _ (.inl mid)).trans ((gather.2 _ (.inl lo)).trans (panel j)))
  have start : PriorHeader.endAddress H G M D first₀=start₀:=by rw [←c.degree];rfl
  have order:=v.into_booked_headers floor
  have priorToMouth:=order.1.trans (order.2.1.trans order.2.2.1)
  have matToMouth:=cash.material.trans (((v.signed).room (v.markEnd floor)).trans priorToMouth)
  have coverage:=v.retained_material_boards floor A adj parts initial prefix R state bands issued bill neighbor start
    matToMouth saved original partLow oldPanel admit.panel admit.capacity admit.bits grown cash.lanes cash.blocks cash.growth headRoom
  have heads:=v.registered_headers floor A mat shape pg chip oldBooks m good input span data home lane group word wideBook pages
    admit.panel admit.capacity admit.bits admit.prior headRoom
  have parentRoom:=fun x i=>v.parent_candidate_room floor c cash
    (priorToMouth.trans (r₄.trans (r₅.trans r₆))) x i
  have selected:=v.sourced_ticket R state bands serial peer floor c A mat shape blocks bound groups orig prior born gathered pg
    cash.lanes room rosters coverage.1 coverage.2.1 (fun x i=>⟨⟨(parentRoom x i).1,(parents x i).1⟩,
      ⟨(parentRoom x i).2,(parents x i).2⟩⟩) coverage.2.2 heads.1 heads.2.1 heads.2.2
  have books:=References.reads (vx₀) (refs₀) oldBooks (l₀).nodes vec₀ m wideBook admit.lanes admit.radix pages
    ((r₁.trans (r₂.trans r₃)).trans_lt firstRoom)
  have ret:=previous_values_read (l₀) (vx₀) shape.operands shape.blocks shape.hosts shape.groups shape.lanes
    (References.returnedValue (vx₀) oldBooks (l₀).nodes) vec₀ gathered books
  exact ⟨selected,fun x p=>ret p x⟩

theorem registered_resolver_keys
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
    (typed : BookPointers oldPages) (cap : 22*(fmt₀).cap+10<2^((l₀).size+2))
    :
    let digits:=fun j h k=>v.matched_role_room R state bands serial peer blocks bound groups orig prior born j h k
      (v.raw_role_room floor A mat shape pg oldBooks chip home group word m (Nat.mul_pos admit.lanes admit.radix) pages j h k) cap
    let raw:=ofBooks oldPages typed
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
  exact v.routed_native_ticket floor w c A mat shape blocks pg m oldPages typed words purchased admit full wide
    reads.2 reads.1 (v.matched_ticket_flags R state bands serial peer blocks bound groups orig prior born) digits

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
