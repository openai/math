import OAI.Hierarchy.DescentSelectedBoardMaterial
import OAI.Hierarchy.DescentSelectedMatchBoard
import OAI.Hierarchy.DescentOriginalSignedPhase
import OAI.Hierarchy.DescentOrdinaryNamedModel
import OAI.Hierarchy.DescentOrdinaryReciprocalHost
import OAI.Hierarchy.DescentDatedSignedMeasuredRun
import OAI.Hierarchy.DescentDatedOriginalIncoming
import OAI.Hierarchy.DescentDatedOriginalMarkIdentity

namespace OAI
/-! The donor board is observed at the original matching date: the selected two colors,
the six birth records, and the original topology are all tied to that same prior stage. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentPacking.PackedMatch
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentDatedAddressBook DescentParallelBase.ParentFilter
open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1100000
attribute [local irreducible] Stage.nativeParts topologyWords Gather.flat terrain spread
  pairNumber slabPacking Stage.slot
variable {F P : Type} [Field F] (v:PhysicalOrdinary F P)
private theorem retainedCapacity {degree sites oldTickets tickets cap fieldBits : ℕ}
    (same : oldTickets = tickets) (budget : Fused.capacity degree sites oldTickets cap ≤ 2^fieldBits) :
    Fused.capacity degree sites tickets cap ≤ 2^fieldBits :=
  same ▸ budget

local notation "phys" => v.withIssuedSigned
local notation "S" => v.schedule
local notation "G" => v.gadget
local notation "A" => v.prior.placement
local notation "T" => (A).stage
local notation "D" => (A).degree
local notation "r" => 2^v.k
local notation "J" => (S).groupCount v.age
local notation "M" => lanes v.payload (v.ticket.installedDonorWidth v.short v.profile)
local notation "H" => v.area.H
local notation "ss" => (phys).signed
local notation "native" => v.prior.order.trans Fin.valEmbedding
local notation "rank" => groupRank Fin.valEmbedding (v.prior.vertex.trans Fin.valEmbedding)
local notation "grp" => Equiv.refl (Fin J)
local notation "peers" => rotor A rank
local notation "home" => scanHomeAt v.nonnegative T
local notation "color" => scanColorAt v.nonnegative T
local notation "addr" => nativeAddress v.nonnegative T
local notation "rr" => BitDescription.scannedRows v.nonnegative T
local notation "K" => 2^(v.k+1)
local notation "s" => shape r D (2*(A).cap) v.profile
local notation "traffic" => nativeTraffic v.world.graph v.world.core home
local notation "fmt" => v.ticket.depotShape v.short
variable (oldFit:Fintype.card v.prior.V≤v.area.H) (R:Fin v.area.H→Fin v.prior.placement.degree→Option (Fin v.area.H))
local notation "hosts" => v.prior.vertex.trans (Fin.castLEEmb oldFit)
variable (selected:(v.prior.placement.stage.result v.nonnegative).Choice)
local notation "lay" => bestLayout (branchWidth G (fun _:(rr).pairs=>(T).z) ((rr).profile selected))
variable {w:ℕ} (m:Memory w) (parts:Bank)

open DescentHaloPackedRebase DescentSharedCableNames
variable (B:v.SelectedBoard oldFit R selected m parts)
variable (choiceEq:HEq selected v.choice) (wide:Fintype.card v.target.V≤ v.withIssuedSigned.signed.hosts)
variable (age:v.age<v.schedule.length) (radix:v.schedule.radix=2^v.k)
local notation "host" => v.target.vertex.trans (Fin.castLEEmb wide)
local notation "chart" => v.issuedSignedChart
local notation "pitch" => (phys).materialPitch
local notation "paths" => (ss).reach
local notation "space" => v.signedLayout.field_room.1
local notation "oldStates" => B.material


private theorem board_path_width : paths<2^(ss).fieldBits :=by
  change breadth D<2^(ss).fieldBits
  have cap : Fused.capacity D (ss).lowSites (ss).tickets (ss).cap≤2^(ss).fieldBits:=space
  unfold Fused.capacity at cap
  omega

private theorem board_ticket_width : (ss).tickets≤2^(ss).fieldBits := v.signedLayout.field_room.2.2.2.1

private theorem board_ticket_count : (ss).tickets=(paths+1)*DepotRAM.Material.roles fmt :=
  congrArg (fun x=>(paths+1)*x) (chart).seats
section DrawnBoard
variable (bands:v.schedule.groupCount v.age=v.withIssuedSigned.signed.groups*(2^v.k))
variable (reciprocal:∀v u j,R v j=some u→∃l,R u l=some v)
variable (positive:0<v.withIssuedSigned.materialPitch) (inside:v.withIssuedSigned.materialPitch≤v.withIssuedSigned.signed.lowSites)
local notation "markedBits" => (phys).markBits chart oldFit bands.symm R

include choiceEq age radix in
theorem selected_drawing :
    ∃pr : ∀h g z,DepotRAM.Material.ParentRoom fmt (phys).materialFormat (oldStates h g)
      (digest (DepotRAM.Material.reverseEntries fmt R h)) z (ss).lowSites (ss).tickets (ss).cap,
      Nonempty (SignedDrawing v.target.placement (v.target.order.trans Fin.valEmbedding) R reciprocal host pitch space
        (fun x j=>(phys).signedIncoming chart rfl R oldStates bands space positive inside pr (x,j))
        (fun x o h g=>(phys).originalParent R oldStates bands pr ((chart).donorSeat o) h (finProdFinEquiv (g,x))) markedBits) :=by
  have marks:=v.original_mark_identity oldFit 0 0 M R age radix bands.symm
  rw [marks]
  have pathWidth := board_path_width v
  have idWidth := board_ticket_width v
  have capacity:Fused.capacity D (ss).lowSites (ss).tickets (ss).cap≤2^(ss).fieldBits:=space
  have ids := board_ticket_count v
  cases v with
  | mk d bits gadget₁ schedule₁ q u eps k date z degree wire hist nz nd W prior he stage₁ c n target link old reference bornBook
      ingress raster vector resolver origin palette repack metadata operandBook signed venue level b short payload unit profile seats =>
    obtain rfl:=link.sourceRate
    obtain rfl:=eq_of_heq link.placement
    have selectedToC : selected = c := eq_of_heq choiceEq
    subst selected
    let port:MeterPort prior:=⟨2^level,oldFit,0,0,DescentSIMDLookup.lanes payload (link.installedDonorWidth short profile)⟩
    rw [ids] at idWidth
    exact OrdinaryLink.originalDrawingAt link port B.win B.live B.named B.small B.winning B.degree B.ordered
      profile B.topo B.matched B.width B.topology B.births B.issued R B.neighbors B.offspring
      _ age radix pathWidth idWidth reciprocal wide _ ids bands capacity

end DrawnBoard

section SelectedModel
variable (reciprocal:∀v u j,R v j=some u→∃l,R u l=some v)

private def presentationNormalized (model : OrdinaryModel v.nonnegative T selected (Fin J × v.prior.V)) : Prop :=
  HEq v.normalize (model.named v.nonnegative T selected v.prior.order)

private def presentationTape (model : OrdinaryModel v.nonnegative T selected (Fin J × v.prior.V)) : Prop :=
  HEq v.ticket.tape (model.namedTape v.nonnegative T selected v.prior.order)

private def presentationSame (model : OrdinaryModel v.nonnegative T selected (Fin J × v.prior.V)) : Prop :=
  v.normalize.result = (model.named v.nonnegative T selected v.prior.order).result

/-- The model and actual typed diagram selected by this physical board. Both
normalization and the original ordering tape are retained along with the diagram. -/
structure ModelPresentation : Type 2 where
  model : OrdinaryModel v.nonnegative T selected (Fin J×v.prior.V)
  normalized : presentationNormalized v selected model
  tape : presentationTape v selected model
  same : presentationSame v selected model
  diagram : Σ α : Type 1, α
  numbers : ℕ→ℕ→ℕ→ℕ→ℕ×ℕ

include oldFit R m parts B choiceEq wide age radix reciprocal in
def selectedModelPresentation : v.ModelPresentation selected :=by
  have pathWidth := board_path_width v
  have idWidth := board_ticket_width v
  have capacity:Fused.capacity D (ss).lowSites (ss).tickets (ss).cap≤2^(ss).fieldBits:=space
  have ids := board_ticket_count v
  cases v with
  | mk d bits gadget₁ schedule₁ q u eps k date z degree wire hist nz nd W prior he stage₁ c n target link old reference bornBook
      ingress raster vector resolver origin palette repack metadata operandBook signed venue level b short payload unit profile seats =>
    obtain rfl:=link.sourceRate
    obtain rfl:=eq_of_heq link.placement
    have selectedToC : selected = c := eq_of_heq choiceEq
    subst selected
    let port:MeterPort prior:=⟨2^level,oldFit,0,0,DescentSIMDLookup.lanes payload (link.installedDonorWidth short profile)⟩
    rw [ids] at idWidth
    let picked:=OrdinaryLink.parent_model link port age radix
    let model:=picked.choose
    let selectedProof:=picked.choose_spec
    let normalized:=selectedProof.2.2
    let drawing:=OrdinaryLink.actualModelDrawing link port B.win B.live B.named B.small B.winning B.degree B.ordered
      profile B.topo B.matched B.width B.topology B.births B.issued R B.neighbors B.offspring
      _ age radix model normalized.choose normalized.choose_spec.1 pathWidth idWidth reciprocal wide (retainedCapacity ids capacity)
    exact ⟨model,selectedProof.1,selectedProof.2.1,normalized.choose,⟨_,drawing⟩,drawing.numbered _
      (OrdinaryLink.model_bounds (next:=target) model normalized.choose)
      (OrdinaryLink.model_shape (next:=target) model normalized.choose).1⟩

end SelectedModel

variable (bands:v.schedule.groupCount v.age=v.withIssuedSigned.signed.groups*(2^v.k))
variable (reciprocal:∀v u j,R v j=some u→∃l,R u l=some v)
variable (positive:0<v.withIssuedSigned.materialPitch) (inside:v.withIssuedSigned.materialPitch≤v.withIssuedSigned.signed.lowSites)
local notation "markedBits" => (phys).markBits chart oldFit bands.symm R

local notation "original" => v.selectedModelPresentation oldFit R selected m parts B choiceEq wide age radix reciprocal

include choiceEq age radix in
def selectedDrawingWitness :
    (pr : ∀h g z,DepotRAM.Material.ParentRoom fmt (phys).materialFormat (oldStates h g)
      (digest (DepotRAM.Material.reverseEntries fmt R h)) z (ss).lowSites (ss).tickets (ss).cap) →
      {D₀ : SignedDrawing v.target.placement (v.target.order.trans Fin.valEmbedding) R reciprocal host pitch space
        (fun x j=>(phys).signedIncoming chart rfl R oldStates bands space positive inside pr (x,j))
        (fun x o h g=>(phys).originalParent R oldStates bands pr ((chart).donorSeat o) h (finProdFinEquiv (g,x))) markedBits // HEq D₀ (original).diagram.2 ∧ D₀.numbered S v.target.valid rfl=(original).numbers} :=by
  have marks:=v.original_mark_identity oldFit 0 0 M R age radix bands.symm
  rw [marks]
  have pathWidth := board_path_width v
  have idWidth := board_ticket_width v
  have capacity:Fused.capacity D (ss).lowSites (ss).tickets (ss).cap≤2^(ss).fieldBits:=space
  have ids := board_ticket_count v
  cases v with
  | mk d bits gadget₁ schedule₁ q u eps k date z degree wire hist nz nd W prior he stage₁ c n target link old reference bornBook
      ingress raster vector resolver origin palette repack metadata operandBook signed venue level b short payload unit profile seats =>
    have sourceRateEq := link.sourceRate
    rcases sourceRateEq with rfl
    have sourceStageEq := eq_of_heq link.placement
    rcases sourceStageEq with rfl
    have selectedToC : selected = c := eq_of_heq choiceEq
    subst selected
    let port:MeterPort prior:=⟨2^level,oldFit,0,0,DescentSIMDLookup.lanes payload (link.installedDonorWidth short profile)⟩
    rw [ids] at idWidth
    intro pr
    refine ⟨OrdinaryLink.originalDrawingAtData link port B.win B.live B.named B.small B.winning B.degree B.ordered
      profile B.topo B.matched B.width B.topology B.births B.issued R B.neighbors B.offspring
      _ age radix pathWidth idWidth reciprocal wide _ ids bands capacity pr,?_,?_⟩
    · exact HEq.trans (OrdinaryLink.originalDrawingAtData_heq link port B.win B.live B.named B.small B.winning
        B.degree B.ordered profile B.topo B.matched B.width B.topology B.births B.issued R B.neighbors B.offspring
        _ age radix pathWidth idWidth reciprocal wide _ ids bands capacity pr)
        (OrdinaryLink.originalDrawingData_heq link port B.win B.live B.named B.small B.winning
          B.degree B.ordered profile B.topo B.matched B.width B.topology B.births B.issued R B.neighbors B.offspring
          _ age radix pathWidth idWidth reciprocal wide (retainedCapacity ids capacity))
    · exact Eq.trans (OrdinaryLink.originalDrawingAtData_numbers link port B.win B.live B.named B.small B.winning
        B.degree B.ordered profile B.topo B.matched B.width B.topology B.births B.issued R B.neighbors B.offspring
        _ age radix pathWidth idWidth reciprocal wide _ ids bands capacity pr)
        (OrdinaryLink.originalDrawingData_numbers link port B.win B.live B.named B.small B.winning
          B.degree B.ordered profile B.topo B.matched B.width B.topology B.births B.issued R B.neighbors B.offspring
          _ age radix pathWidth idWidth reciprocal wide (retainedCapacity ids capacity))

include choiceEq age radix in
def selectedDrawingData :
    (pr : ∀h g z,DepotRAM.Material.ParentRoom fmt (phys).materialFormat (oldStates h g)
      (digest (DepotRAM.Material.reverseEntries fmt R h)) z (ss).lowSites (ss).tickets (ss).cap) →
      SignedDrawing v.target.placement (v.target.order.trans Fin.valEmbedding) R reciprocal host pitch space
        (fun x j=>(phys).signedIncoming chart rfl R oldStates bands space positive inside pr (x,j))
        (fun x o h g=>(phys).originalParent R oldStates bands pr ((chart).donorSeat o) h (finProdFinEquiv (g,x))) markedBits :=fun pr=>(v.selectedDrawingWitness oldFit R selected m parts B choiceEq wide age radix bands reciprocal positive inside pr).val

theorem retainedPitch_pos : 0<pitch :=by
    change 0<(2^(v.k+1)-1)*(2^packExponent 20 v.stage.Δ+2)
    have p:=Nat.one_lt_two_pow' v.k
    exact Nat.mul_pos (by omega) (Nat.succ_pos _)

theorem retainedPitch_le : pitch≤ (ss).lowSites :=by
    change (2^(v.k+1)-1)*(2^packExponent 20 v.stage.Δ+2)≤2^(v.k+1)*(2^packExponent 20 D+2)
    rw [(Stage.Dated.Meter.ticket_shape v.ticket).2]
    exact Nat.mul_le_mul_right _ (Nat.sub_le ..)


/-- The actual matched board fixes the parent candidate at each (receiver, donor path, original role). -/
def retainedDrawing :=
  v.selectedDrawingData oldFit R selected m parts B choiceEq wide age radix bands
    reciprocal v.retainedPitch_pos v.retainedPitch_le
    (v.selected_drawing oldFit R selected m parts B choiceEq wide age radix bands
      reciprocal v.retainedPitch_pos v.retainedPitch_le).choose
local notation "drawing₀" => v.retainedDrawing oldFit R selected m parts B choiceEq wide age radix bands reciprocal
/-- The retained upper drawing is the specific original physical drawing
of the model recorded at this very board. -/
theorem retained_origin : HEq (v.retainedDrawing oldFit R selected m parts B choiceEq wide age radix bands reciprocal)
    (original).diagram.2 :=by
  exact (v.selectedDrawingWitness oldFit R selected m parts B choiceEq wide age radix bands reciprocal
    v.retainedPitch_pos v.retainedPitch_le (v.selected_drawing oldFit R selected m parts B choiceEq wide age radix bands
      reciprocal v.retainedPitch_pos v.retainedPitch_le).choose).property.1


def retainedSerial (x:Fin (phys).material.blocks) (j:Fin (breadth (fmt).degree*DepotRAM.Material.roles fmt)) :=
  (drawing₀).serial S v.target.valid (x.cast (chart).blocks.symm) ((phys).parentSlot chart j)

def retainedPeer (x:Fin (phys).material.blocks) (j:Fin (breadth (fmt).degree*DepotRAM.Material.roles fmt)) :=
  (drawing₀).peer S v.target.valid (x.cast (chart).blocks.symm) ((phys).parentSlot chart j)

/-- The two literal W columns agree with the port and role of the original
measured diagram even after its parent-ticket and coordinate reindexing. -/
theorem retained_numbers (x:Fin (phys).material.blocks) (j:Fin (breadth (fmt).degree*DepotRAM.Material.roles fmt))
    (h:Fin (ss).hosts) (g:Fin (ss).groups) :
    ((v.retainedPeer oldFit R selected m parts B choiceEq wide age radix bands reciprocal x j h g).val,
     (v.retainedSerial oldFit R selected m parts B choiceEq wide age radix bands reciprocal x j h g).val)=
      (original).numbers x.val ((phys).parentSlot chart j).val h.val g.val :=by
  have same:=(v.selectedDrawingWitness oldFit R selected m parts B choiceEq wide age radix bands reciprocal
    v.retainedPitch_pos v.retainedPitch_le (v.selected_drawing oldFit R selected m parts B choiceEq wide age radix bands
      reciprocal v.retainedPitch_pos v.retainedPitch_le).choose).property.2
  have atRole := congrFun (congrFun (congrFun (congrFun same x.val)
    ((phys).parentSlot chart j).val) h.val) g.val
  exact ((drawing₀).numbered_entry S v.target.valid rfl (x.cast (chart).blocks.symm)
    ((phys).parentSlot chart j) h g).symm.trans atRole


variable (floor:ℕ) (input:Stage.Dated.Operands) (count adj:Bank)
local notation "src" => (⟨count,input.roster,input.hubs⟩:DescentOrdinaryVenueReturn.Sources)
local notation "base" => (phys).markEnd floor
local notation "rankBank" => PriorHeader.reverseRank H (ss).groups (ss).lanes D ((phys).donorEnd floor)
local notation "out" => (v.signedPredecessor floor input count parts adj w).image m
local notation "program" => (phys).signedPhase floor chart w

include B choiceEq age radix reciprocal in
/-- The signed return of the selected ordinary stage. The real winner, topology,
six births and retained prior material determine all banks, including empty sockets. -/
theorem signed_original_run (cash:(phys).SignedRoom floor w)
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
    (place:lower≤(phys).donorEnd floor) :
    (program).Runs out ∧
    (∀x j,DescentPackedColony.Reads ((ss).page base x j) (fun h g=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed v.target.placement (v.target.order.trans Fin.valEmbedding) S v.target.valid
        (Equiv.refl (Fin ((S).groupCount (v.age+1)))).toEmbedding host x j h g)) (ss).lanes ((program).image out)) ∧
    (∀a,a<base ∨ (phys).signedEnd floor≤a→(program).image out a=out a) ∧ CheapCode (program).program :=by
  have pitchPositive:=v.retainedPitch_pos
  have pitchRoom:=v.retainedPitch_le
  obtain ⟨pr,drawing⟩:=v.selected_drawing oldFit R selected m parts B choiceEq wide age radix cash.groups
    reciprocal pitchPositive pitchRoom
  exact v.signed_drawing_run (wide:=wide) (R:=R) (symm:=reciprocal) (floor:=floor) (input:=input)
    (count:=count) (parts:=parts) (adj:=adj) (m:=m) (state:=B.material) (cash:=cash) (pr:=pr)
    (positive:=pitchPositive) (inside:=pitchRoom) (oldFit:=oldFit)
    drawing pre material past B.source existing room mark B.live oldMarks newDegree matcher
    precision lower old wires countRead countLow place

local notation "paid" => v.signedReturn (floor:=floor) (input:=input) (count:=count) (parts:=parts) (adj:=adj) w

include B choiceEq age radix reciprocal in
theorem signed_from_match (cash:(phys).SignedRoom floor w)
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
    (place:lower≤(phys).donorEnd floor) :
    (paid).Runs m ∧
    (∀x j,DescentPackedColony.Reads ((ss).page base x j) (fun h g=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed v.target.placement (v.target.order.trans Fin.valEmbedding) S v.target.valid
        (Equiv.refl (Fin ((S).groupCount (v.age+1)))).toEmbedding host x j h g)) (ss).lanes ((paid).image m)) ∧
    (∀a,a<(phys).donorEnd floor ∨ (phys).signedEnd floor≤a→(paid).image m a=m a) ∧ CheapCode (paid).program :=by
  have before:=v.signed_predecessor_any floor input count parts adj m pre material room mark
  have phase:=v.signed_original_run (oldFit:=oldFit) (R:=R) (selected:=selected) (m:=m) (parts:=parts) (B:=B)
    (choiceEq:=choiceEq) (wide:=wide) (age:=age) (radix:=radix) (reciprocal:=reciprocal)
    (floor:=floor) (input:=input) (count:=count) (adj:=adj) cash pre material past existing room mark oldMarks newDegree matcher precision lower old wires
    countRead countLow place
  have small:(phys).donorEnd floor≤base:=
    (((phys).signed_stage_paid floor).1.trans ((phys).signed_stage_paid floor).2.1).trans ((phys).markShape.low _)
  have end_:base≤(phys).signedEnd floor:=(ss).room base
  refine ⟨NativePhase.seq_runs _ _ m before.1 phase.1,phase.2.1,?_,(paid).cheap⟩
  intro a outside
  exact (phase.2.2.1 a (outside.imp (fun lt=>lt.trans_le small) id)).trans
    (before.2 a (outside.imp id (end_.trans ·)))

include choiceEq age radix in
/-- The two retained original input rows are genuine prior reads in the same
final signed RAM used by the next date. Both signs address the first grain of
their common parent. -/
theorem retained_from_match (cash:(phys).SignedRoom floor w)
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
    (place:lower≤(phys).donorEnd floor) :
    (∀x j,
      (((phys).parentSerial floor chart x j).Fits w ((phys).signedEnd floor) ∧
        DescentPackedZip.Source ((phys).parentSerial floor chart x j)
          (v.retainedSerial oldFit R selected m parts B choiceEq wide age radix cash.groups reciprocal x j) (ss).lanes ((paid).image m)) ∧
      (((phys).parentPeer floor chart x j).Fits w ((phys).signedEnd floor) ∧
        DescentPackedZip.Source ((phys).parentPeer floor chart x j)
          (v.retainedPeer oldFit R selected m parts B choiceEq wide age radix cash.groups reciprocal x j) (ss).lanes ((paid).image m))) ∧
    (paid).Runs m ∧
    (∀x j,DescentPackedColony.Reads ((ss).page base x j) (fun h g=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed v.target.placement (v.target.order.trans Fin.valEmbedding) S v.target.valid
        (Equiv.refl (Fin ((S).groupCount (v.age+1)))).toEmbedding host x j h g)) (ss).lanes ((paid).image m)) ∧
    (∀a,a<(phys).donorEnd floor ∨ (phys).signedEnd floor≤a→(paid).image m a=m a) ∧ CheapCode (paid).program :=by
  let witness:=v.selected_drawing oldFit R selected m parts B choiceEq wide age radix cash.groups reciprocal
    v.retainedPitch_pos v.retainedPitch_le
  let d₀:=v.retainedDrawing oldFit R selected m parts B choiceEq wide age radix cash.groups reciprocal
  have reads:=v.signed_drawing_heads (wide:=wide) (R:=R) (symm:=reciprocal) (floor:=floor) (input:=input)
    (count:=count) (parts:=parts) (adj:=adj) (m:=m) (state:=B.material) (cash:=cash) (pr:=witness.choose)
    (positive:=v.retainedPitch_pos) (inside:=v.retainedPitch_le) (oldFit:=oldFit)
    d₀ pre material past B.source existing room mark B.live oldMarks newDegree matcher
    precision lower old wires countRead countLow place
  exact ⟨reads.1,v.signed_from_match (oldFit:=oldFit) (R:=R) (selected:=selected) (m:=m) (parts:=parts) (B:=B)
    (choiceEq:=choiceEq) (wide:=wide) (age:=age) (radix:=radix) (reciprocal:=reciprocal)
    (floor:=floor) (input:=input) (count:=count) (adj:=adj) cash pre material past existing room mark oldMarks newDegree matcher
    precision lower old wires countRead countLow place⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
