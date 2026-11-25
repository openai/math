import OAI.Hierarchy.DescentDatedRetainedHeaderFrame
import OAI.Hierarchy.DescentDatedSignedSelectedBoard

namespace OAI
/-! Complete input fields six and seven for the original dated operand at the physical header boundary. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentDatedAddressBook DescentParallelBase.ParentFilter
open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8500
set_option cleanup.letToHave false
variable {F P : Type} [Field F] (v:PhysicalOrdinary F P)
set_option hygiene false in
local notation "phys" => v.withIssuedSigned
set_option hygiene false in
local notation "S" => v.schedule
set_option hygiene false in
local notation "G" => v.gadget
set_option hygiene false in
local notation "A" => v.prior.placement
set_option hygiene false in
local notation "T" => (A).stage
set_option hygiene false in
local notation "D" => (A).degree
set_option hygiene false in
local notation "r" => 2^v.k
set_option hygiene false in
local notation "J" => (S).groupCount v.age
set_option hygiene false in
local notation "M" => (phys).material.oldLanes
set_option hygiene false in
local notation "H" => v.area.H
set_option hygiene false in
local notation "ss" => (phys).signed
set_option hygiene false in
local notation "native" => v.prior.order.trans Fin.valEmbedding
set_option hygiene false in
local notation "rank" => groupRank Fin.valEmbedding (v.prior.vertex.trans Fin.valEmbedding)
set_option hygiene false in
local notation "grp" => Equiv.refl (Fin J)
set_option hygiene false in
local notation "peers" => rotor A rank
set_option hygiene false in
local notation "home" => scanHomeAt v.nonnegative T
set_option hygiene false in
local notation "color" => scanColorAt v.nonnegative T
set_option hygiene false in
local notation "addr" => nativeAddress v.nonnegative T
set_option hygiene false in
local notation "rr" => BitDescription.scannedRows v.nonnegative T
set_option hygiene false in
local notation "K" => 2^(v.k+1)
set_option hygiene false in
local notation "s" => shape r D (2*(A).cap) v.profile
set_option hygiene false in
local notation "traffic" => nativeTraffic v.world.graph v.world.core home
set_option hygiene false in
local notation "fmt" => v.ticket.depotShape v.short
variable (oldFit:Fintype.card v.prior.V≤H) (R:Fin H→Fin D→Option (Fin H))
set_option hygiene false in
local notation "hosts" => v.prior.vertex.trans (Fin.castLEEmb oldFit)
variable (selected:((T).result v.nonnegative).Choice)
set_option hygiene false in
local notation "lay" => bestLayout (branchWidth G (fun _:(rr).pairs=>(T).z) ((rr).profile selected))
variable {w:ℕ} (m:Memory w) (parts:Bank)

variable (B:v.SelectedBoard oldFit R selected m parts)
variable (choiceEq:HEq selected v.choice) (wide:Fintype.card v.target.V≤ (ss).hosts)
variable (age:v.age<(S).length) (radix:(S).radix=r) (bands:J=(ss).groups*r)
variable (reciprocal:∀v u j,R v j=some u→∃l,R u l=some v)
set_option hygiene false in
local notation "host" => v.target.vertex.trans (Fin.castLEEmb wide)
set_option hygiene false in
local notation "chart" => v.issuedSignedChart
set_option hygiene false in
local notation "pitch" => (phys).materialPitch
set_option hygiene false in
local notation "paths" => (ss).reach
set_option hygiene false in
local notation "space" => v.signedLayout.field_room.1
set_option hygiene false in
local notation "oldStates" => B.material
set_option hygiene false in
local notation "markedBits" => (phys).markBits chart oldFit bands.symm R
variable (positive:0<pitch) (inside:pitch≤ (ss).lowSites)

variable (floor:ℕ) (input:Stage.Dated.Operands) (count adj:Bank)
set_option hygiene false in
local notation "src" => (⟨count,input.roster,input.hubs⟩:DescentOrdinaryVenueReturn.Sources)
set_option hygiene false in
local notation "base" => (phys).markEnd floor
set_option hygiene false in
local notation "rankBank" => PriorHeader.reverseRank H (ss).groups (ss).lanes D ((phys).donorEnd floor)
set_option hygiene false in
local notation "out" => (v.signedPredecessor floor input count parts adj w).image m
set_option hygiene false in
local notation "program" => (phys).signedPhase floor chart w

set_option hygiene false in
local notation "paid" => v.signedReturn (floor:=floor) (input:=input) (count:=count) (parts:=parts) (adj:=adj) w

include choiceEq age radix in
theorem original_heads_at_headers (cash:(phys).SignedRoom floor w)
    (pre:PriorHeader.Room adj H (ss).groups (ss).lanes D ((phys).donorEnd floor) w)
    (material:(phys).MaterialRoom ((phys).materialStart floor) parts rankBank w)
    (past:parts.base+parts.size≤(phys).donorEnd floor)
    (existing:∀h j,m (adj.base+h.val*D+j.val)=(number (R h j):Computability.VPVNP.BurstRAM.Word w))
    (room:DescentOrdinaryVenueReturn.Room src ((phys).materialEnd floor) H v.area.D v.venue.hosts v.venue.degree w)
    (mark:(phys).MarkRoom floor input w) (oldMarks:0<(phys).markShape.oldLanes)
    (newDegree:v.venue.degree=v.target.placement.degree) (matcher:v.area.Space input w floor)
    (precision lower:ℕ) (old:stageVenue v.prior oldFit input (phys).markShape.oldLanes precision lower
      (v.prior.venueRoster oldFit) m)
    (wires:∀(x:Fin (2^v.k))(j:Fin (2*(A).cap)),(input.wire x.val j.val).base+
      H*chunks J (phys).markShape.oldLanes≤lower)
    (countRead:m count.base=(Fintype.card v.prior.V:Computability.VPVNP.BurstRAM.Word w)) (countLow:count.base<lower)
    (place:lower≤(phys).donorEnd floor) (entry:(phys).ArgumentEntry) («matching»:entry.Match phys floor)
    (refs:(phys).SourceReferences) (orig:(phys).SourceMasks)
    (headerRoom:(phys).OperandHeaderRoom floor entry «matching» refs orig w) :
    let later:=((phys).toOperandHeaders floor entry «matching» refs orig headerRoom).image ((paid).image m)

    (∀x j,
      (((phys).parentSerial floor chart x j).Fits w ((phys).operandHeaderEnd floor) ∧
        DescentPackedZip.Source ((phys).parentSerial floor chart x j)
          (v.retainedSerial oldFit R selected m parts B choiceEq wide age radix cash.groups reciprocal x j) (ss).lanes later) ∧
      (((phys).parentPeer floor chart x j).Fits w ((phys).operandHeaderEnd floor) ∧
        DescentPackedZip.Source ((phys).parentPeer floor chart x j)
          (v.retainedPeer oldFit R selected m parts B choiceEq wide age radix cash.groups reciprocal x j) (ss).lanes later)) ∧
    ∀a,a<(phys).material.endAddress ((phys).materialStart floor)→
      later a=((phys).materialAt ((phys).materialStart floor) parts ((phys).operandRanks floor).reverseRank w).image
        ((PriorHeader.phase H (ss).groups (ss).lanes D ((phys).donorEnd floor) adj w).image m) a :=by
  intro later
  have read:=v.retained_from_match (oldFit:=oldFit) (R:=R) (selected:=selected) (m:=m) (parts:=parts) (B:=B)
    (choiceEq:=choiceEq) (wide:=wide) (age:=age) (radix:=radix) (reciprocal:=reciprocal)
    (floor:=floor) (input:=input) (count:=count) (adj:=adj) cash pre material past existing room mark oldMarks newDegree matcher
    precision lower old wires countRead countLow place
  refine ⟨?_,v.material_at_operand_headers floor input count parts adj m entry «matching» refs orig headerRoom cash material room mark⟩
  intro x j
  have saved:=read.1 x j
  exact ⟨(phys).retained_header_source floor entry «matching» refs orig headerRoom ((paid).image m) _ _ saved.1.1 saved.1.2,
    (phys).retained_header_source floor entry «matching» refs orig headerRoom ((paid).image m) _ _ saved.2.1 saved.2.2⟩
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
