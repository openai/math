import OAI.Hierarchy.DescentDatedPhysicalWalkValue
import OAI.Hierarchy.DescentDatedSortedBroadcast
import OAI.Hierarchy.DescentDatedSortedOperandAdapter
import OAI.Hierarchy.DescentDatedSampledParentNumbers
import OAI.Hierarchy.DescentDatedSampledOldSocketCore

namespace OAI
/-! # Selection of a retained cable by the physical ordinary ticket reader -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedOperandReadPipeline DescentDatedOperandCoordinates DescentHaloWalkRAM
open DescentDatedSourcePathDirectory DescentSharedCableNames DescentRawCablePanel DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I)
local notation "e" => v.material
local notation "fmt" => v.ticket.depotShape v.short
local notation "g" => v.ticketReadGeometry
local notation "l" => v.resolver
local notation "P" => breadth (fmt).degree
local notation "seats" => P*DepotRAM.Material.roles fmt
local notation "value" => (Fin (e).hosts→Fin (e).groups→Cell (e).fieldBits)
variable (blocks : v.resolver.blocks=v.material.blocks) (bound : v.resolver.hosts≤v.material.hosts) (groups : v.resolver.groups=v.material.groups)
    (R : Fin v.material.oldHosts→Fin (v.ticket.depotShape v.short).degree→Option (Fin v.material.oldHosts))
    (state : Fin v.material.oldHosts→Fin v.material.oldGroups→DepotRAM.Parts (v.ticket.depotShape v.short)) (bands : v.material.oldGroups=v.material.groups*v.material.blocks)
    (serial peer : Fin v.material.blocks→Fin (breadth (v.ticket.depotShape v.short).degree*DepotRAM.Material.roles (v.ticket.depotShape v.short))→(Fin v.material.hosts → Fin v.material.groups → Cell v.material.fieldBits))
    (orig : Fin v.resolver.jobs→Fin 6→Values v.ticketReadGeometry v.operandShortBits) (prior : Fin v.resolver.jobs→Fin 4→Values v.ticketReadGeometry (v.resolver.size+2))
    (birth : Fin v.resolver.jobs→Fin 3→Values v.ticketReadGeometry v.bornBook.bits)
local notation "record" => v.sampleHeads blocks bound groups orig prior birth
  (v.wideMaterialValues R state bands serial peer) (v.narrowValue R)
local notation "data" => v.originalValues record
variable (j : Fin v.resolver.jobs) (h : Fin v.resolver.hosts) (y : Fin v.resolver.groups) (recv : Fin v.material.oldHosts)
local notation "h₀" => h.castLE bound
local notation "y₀" => y.cast groups
local notation "x₀" => v.receiverBlock blocks j
local notation "pack" h => state h ((finProdFinEquiv (y₀,x₀)).cast bands.symm)
variable (atHost : DepotRAM.Material.Route.receiver v.material.oldHosts v.materialPitch (h.castLE bound)=some recv)

include atHost in
/-- The retained header, reached donor and anchor are sampled at their original
material addresses before the native selector examines the W ordinal. -/
private theorem sampled_old_table_values
    (actor source : Fin (e).oldHosts) (root p : Fin P) (x : Fin (fmt).blocks)
    (priorPeer neighbor : Fin (fmt).degree) (first old : Fin (fmt).cap) (target : Bool)
    (z : Ticket.SocketSeat (fmt).blocks (fmt).cap)
    (visited : Gather.select (Gather.reaching R) recv root=some actor)
    (signed : DepotRAM.Parts fmt) (retained : (pack actor).cables=signed.cables)
    (signedRows :
      let row (f : Fin 4) := DescentDatedOperandPages.law fmt v.profile (e).fieldBits
        (DescentDatedOperandPages.header fmt x priorPeer first f).val (DepotRAM.combine fmt signed)
      (row 3).val=old.val+1 ∧ (row 2).val=target.toNat ∧ (target=true→(row 1).val=neighbor.val+1))
    (path : DescentDatedSourcePathDirectory.value (Gather.reaching R) recv root
      (shortPath (if target then neighbor.castSucc else Fin.last (fmt).degree))=p.val+1)
    (donated : Gather.select (Gather.reaching R) recv p=some source)
    (anchorPage : let mode : Fin 2:=if target then 1 else 0
      (DescentDatedOperandPages.law fmt v.profile (e).fieldBits
        (DescentDatedOperandPages.anchor fmt x old mode 4).val (DepotRAM.combine fmt (pack source))).val=
        Ticket.anchor false z 4) :
    OldSocketRows g data j h y root p x priorPeer neighbor first old target z :=by
  let i:=finProdFinEquiv (root,finProdFinEquiv (x,finProdFinEquiv (priorPeer,first)))
  have oldRow (f : Fin 4) : ((data).old j f i h y).val=
      (DescentDatedOperandPages.law fmt v.profile (e).fieldBits
        (DescentDatedOperandPages.header fmt x priorPeer first f).val (DepotRAM.combine fmt signed)).val :=by
    have ix : v.matchOldIndex i f=(root,DescentDatedOperandPages.header fmt x priorPeer first f):=by
      simp [i,matchOldIndex]
    rw [v.sampled_old_number blocks bound groups R state bands serial peer orig prior birth j h y recv actor
      atHost i f (by simpa only [ix] using visited),ix]
    exact congrArg Fin.val (DescentDatedOperandPages.header_at_cables fmt _ _ x priorPeer first f _ _ retained)
  constructor
  · obtain ⟨slot,side,next⟩:=signedRows
    exact ⟨(oldRow 3).trans slot,(oldRow 2).trans side,fun ht=>(oldRow 1).trans (next ht)⟩
  · let step:=if target then neighbor.castSucc else Fin.last (fmt).degree
    refine (v.original_path_number record (finProdFinEquiv (root,step)) h y).trans ?_
    change (v.narrowValue R (.inl (finProdFinEquiv (root,step))) h₀ y₀).val=_
    simpa only [narrowValue,Equiv.symm_apply_apply,atHost,Option.elim_some,token] using path
  · let a:=finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,(if target then 1 else 0:Fin 3))))
    let mode : Fin 2:=if target then 1 else 0
    have ix : v.matchAnchorIndex a 4=(p,DescentDatedOperandPages.anchor fmt x old mode 4):=by
      cases target <;> simp [a,mode,matchAnchorIndex,DescentDatedOperandPages.matcherIndex]
    change ((data).anchor j 4 a h y).val=_
    rw [v.sampled_anchor_number blocks bound groups R state bands serial peer orig prior birth j h y recv source
      atHost a 4 (by simpa only [ix] using donated),ix]
    exact anchorPage

include atHost in
/-- The matched row and both native argument digits use this same selected seat.
The W decoder gives the first raw walk to the old actor. The signed page chooses
whether the source-path decoder stays there or follows its old neighbor. -/
theorem sampled_old_socket
    (actor source : Fin (e).oldHosts) (root p : Fin P) (x : Fin (fmt).blocks)
    (priorPeer neighbor : Fin (fmt).degree) (first old : Fin (fmt).cap) (target : Bool) (chunk : ℕ)
    (z : Ticket.SocketSeat (fmt).blocks (fmt).cap)
    (cause : (orig j 0 h y).val=1) (walk : (orig j 1 h y).val=root.val)
    (block : (orig j 2 h y).val=x.val)
    (header : ∀f,(prior j f h y).val=(DescentOperandStateBanks.Pointer.cable priorPeer.val first.val chunk).header f)
    (visited : Gather.select (Gather.reaching R) recv root=some actor)
    (signed : DepotRAM.Parts fmt) (retained : (pack actor).cables=signed.cables)
    (signedRows :
      let row (f : Fin 4) := DescentDatedOperandPages.law fmt v.profile (e).fieldBits
        (DescentDatedOperandPages.header fmt x priorPeer first f).val (DepotRAM.combine fmt signed)
      (row 3).val=old.val+1 ∧ (row 2).val=target.toNat ∧ (target=true→(row 1).val=neighbor.val+1))
    (path : DescentDatedSourcePathDirectory.value (Gather.reaching R) recv root
      (shortPath (if target then neighbor.castSucc else Fin.last (fmt).degree))=p.val+1)
    (donated : Gather.select (Gather.reaching R) recv p=some source)
    (anchorPage : let mode : Fin 2:=if target then 1 else 0
      (DescentDatedOperandPages.law fmt v.profile (e).fieldBits
        (DescentDatedOperandPages.anchor fmt x old mode 4).val (DepotRAM.combine fmt (pack source))).val=
        Ticket.anchor false z 4) :
    let a:=finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,(if target then 1 else 0:Fin 3))))
    let raw:=finProdFinEquiv (p,Ticket.seatNo z)
    (rawKey g data j h y).val=Ticket.socket p false z ∧
      ((data).origin j 0 h y).val=1 ∧ ((data).prior j 0 h y).val=1 ∧
      (anchorChoice g data j h y).val=a.val+1 ∧ (pathV g data j 0 h y).val=p.val+1 ∧
      ∀ f,rawV g data j f h y=(data).raw j f raw h y :=by
  have head (f : Fin 4) : ((data).prior j f h y).val=
      (DescentOperandStateBanks.Pointer.cable priorPeer.val first.val chunk).header f :=
    (v.original_prior_number record j f h y).trans (header f)
  have rows:=v.sampled_old_table_values blocks bound groups R state bands serial peer orig prior birth j h y recv
    atHost actor source root p x priorPeer neighbor first old target z visited signed retained signedRows path donated anchorPage
  exact sampled_old_rows_socket g data j h y root p x priorPeer neighbor first old target z chunk cause walk block head rows

include atHost in
theorem sampled_old_sorted_socket
    (actor source : Fin (e).oldHosts) (ordinal root p : Fin P) (x : Fin (fmt).blocks)
    (priorPeer neighbor : Fin (fmt).degree) (first old : Fin (fmt).cap) (target : Bool) (chunk : ℕ)
    (z : Ticket.SocketSeat (fmt).blocks (fmt).cap)
    (cause : (orig j 0 h y).val=1) (stamped : (orig j 1 h y).val=ordinal.val)
    (sorted : DescentSortedRoster.indexed (Gather.reaching R) recv ordinal=some actor)
    (block : (orig j 2 h y).val=x.val)
    (header : ∀f,(prior j f h y).val=(DescentOperandStateBanks.Pointer.cable priorPeer.val first.val chunk).header f)
    (visited : Gather.select (Gather.reaching R) recv root=some actor)
    (signed : DepotRAM.Parts fmt) (retained : (pack actor).cables=signed.cables)
    (signedRows :
      let row (f : Fin 4) := DescentDatedOperandPages.law fmt v.profile (e).fieldBits
        (DescentDatedOperandPages.header fmt x priorPeer first f).val (DepotRAM.combine fmt signed)
      (row 3).val=old.val+1 ∧ (row 2).val=target.toNat ∧ (target=true→(row 1).val=neighbor.val+1))
    (path : DescentDatedSourcePathDirectory.value (Gather.reaching R) recv root
      (shortPath (if target then neighbor.castSucc else Fin.last (fmt).degree))=p.val+1)
    (donated : Gather.select (Gather.reaching R) recv p=some source)
    (anchorPage : let mode : Fin 2:=if target then 1 else 0
      (DescentDatedOperandPages.law fmt v.profile (e).fieldBits
        (DescentDatedOperandPages.anchor fmt x old mode 4).val (DepotRAM.combine fmt (pack source))).val=
        Ticket.anchor false z 4) :
    let normalized:=SortedInput.values g data (v.walkValues (Gather.reaching R))
    let a:=finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,(if target then 1 else 0:Fin 3))))
    let raw:=finProdFinEquiv (p,Ticket.seatNo z)
    (rawKey g normalized j h y).val=Ticket.socket p false z ∧
      (normalized.origin j 0 h y).val=1 ∧ (normalized.prior j 0 h y).val=1 ∧
      (anchorChoice g normalized j h y).val=a.val+1 ∧ (pathV g normalized j 0 h y).val=p.val+1 ∧
      ∀ f,rawV g normalized j f h y=normalized.raw j f raw h y :=by
  have head (f : Fin 4) : ((data).prior j f h y).val=
      (DescentOperandStateBanks.Pointer.cable priorPeer.val first.val chunk).header f :=
    (v.original_prior_number record j f h y).trans (header f)
  have rows:=v.sampled_old_table_values blocks bound groups R state bands serial peer orig prior birth j h y recv
    atHost actor source root p x priorPeer neighbor first old target z visited signed retained signedRows path donated anchorPage
  have held : DepotRAM.Material.Route.receiver (e).oldHosts v.materialPitch h=some recv:=atHost
  exact sampled_old_sorted_rows_socket g data j h y root p x priorPeer neighbor first old target z
    (Gather.reaching R) recv actor ordinal (v.walkValues (Gather.reaching R)) chunk cause stamped sorted visited
    (v.sampled_walk_number R h y recv actor ordinal root held sorted visited) block head rows

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
