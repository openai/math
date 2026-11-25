import OAI.Hierarchy.DescentDatedSampledParentNumbers
import OAI.Hierarchy.DescentDatedSortedOperandAdapter
import OAI.Hierarchy.DescentDatedSampledBirthSocketCore
import OAI.Hierarchy.DescentDatedPhysicalWalkValue

namespace OAI
/-! # The original newborn operand selects its actual matched anchor after W ordinal conversion -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryOriginPorts DescentOrdinaryOriginMask
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

local notation "inverse" => v.walkValues (Gather.reaching R)
local notation "fixed" => SortedInput.values g data inverse

include atHost in
theorem sampled_birth_socket
    (chart : Return) (ordinal : Fin (breadth chart.degree)) (x₁ : Fin (2^chart.depth))
    (seat : Fin chart.capacity) (party : Fin 6) (node : Fin chart.newNodes)
    (word : Cell (chart.ordinalBits*chart.newNodes))
    (stamp : ((encode chart.ordinalBits chart.newNodes).symm word node).val=
      (candidate chart ordinal x₁ (.inr (seat,party))).val+1)
    (origin : ∀f,orig j f h y=readLaw chart (g).digitBits node f word)
    (s p : Fin P) (x : Fin (fmt).blocks) (old : Fin (fmt).cap) (donor : Fin (e).oldHosts)
    (ordinalId : ordinal.val=s.val) (blockId : x₁.val=x.val) (seatId : seat.val=old.val)
    (width : max 2 (max ordinal.val (max x₁.val seat.val))<2^(g).digitBits)
    (sorted : DescentSortedRoster.indexed (Gather.reaching R) recv s=some donor)
    (livePath : Gather.select (Gather.reaching R) recv p=some donor)
    (B : DescentOrdinaryBorn.Spec) (arg scale prof : ℕ) (m : DescentOrdinaryBorn.Mouth)
    (live : DescentOrdinaryBorn.mouth B scale prof party arg=some m)
    (priorRoom : 1<2^((l).size+2)) (mouthRoom : 11≤2^v.bornBook.bits)
    (header : (prior j 0 h y).val=(DescentOrdinaryBorn.field B ((l).size+2) 0 arg scale prof party).val)
    (ports : ∀f,(birth j f h y).val=(DescentOrdinaryBorn.RolePorts.value v.bornBook.bits (some m) f).val)
    (second : Bool) (side : m.anchor.val=second.toNat)
    (z : Ticket.SocketSeat (fmt).blocks (fmt).cap) (mouthRole : m.rawRole=z.2.2.val)
    (anchorPage : let index:=if second then DescentDatedOperandPages.sibling fmt x old 4
      else DescentDatedOperandPages.anchor fmt x old 0 4
      (DescentDatedOperandPages.law fmt v.profile (e).fieldBits index.val (DepotRAM.combine fmt (pack donor))).val=
        Ticket.anchor true z 4) :
    let a:=finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,(if second then 2 else 0:Fin 3))))
    let raw:=finProdFinEquiv (p,Ticket.seatNo z)
    (rawKey g fixed j h y).val=Ticket.socket p true z ∧ ((fixed).origin j 0 h y).val=2 ∧
      ((fixed).prior j 0 h y).val=1 ∧ ((fixed).mouth j 1 h y).val=z.2.2.val ∧
      (anchorChoice g fixed j h y).val=a.val+1 ∧ ((fixed).origin j 1 h y).val+1=p.val+1 ∧
      ∀f,rawV g fixed j f h y=(fixed).raw j f raw h y :=by
  apply sampled_birth_sorted_rows_socket g data j h y v.materialPitch (Gather.reaching R) recv donor
    chart ordinal x₁ seat party node word stamp origin s p x old ordinalId blockId seatId width
    atHost sorted livePath (v.sampled_walk_fits p) B arg scale prof m live ((l).size+2) v.bornBook.bits
    priorRoom mouthRoom ((v.original_prior_number record j 0 h y).trans header)
    (fun f=>(v.original_mouth_number record j f h y).trans (ports f)) second side z mouthRole
  intro a
  let col:=if second then DescentDatedOperandPages.sibling fmt x old 4 else DescentDatedOperandPages.anchor fmt x old 0 4
  have ix : v.matchAnchorIndex a 4=(p,col):=DescentDatedOperandPages.matcher_birth_index fmt p x old second 4
  rw [v.sampled_anchor_number blocks bound groups R state bands serial peer orig prior birth j h y recv donor
    atHost a 4 (by simpa only [ix] using livePath),ix]
  exact anchorPage

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
