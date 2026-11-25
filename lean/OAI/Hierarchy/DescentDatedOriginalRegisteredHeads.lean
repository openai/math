import OAI.Hierarchy.DescentDatedRegisteredWalkBanks
import OAI.Hierarchy.DescentDatedRetainedOriginalHeads
import OAI.Hierarchy.DescentDatedRegisteredTicketBoard
import OAI.Hierarchy.DescentOrdinaryMountedInlet

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentDatedAddressBook DescentParallelBase.ParentFilter
open DescentDatedPriorOperand DescentPackedColony DescentDatedOperandReadPipeline DescentOperandVectorArena DescentOperandStateBanks
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

/-- The returned signed image still supplies the exact old adjacency consumed by the W inlet. -/
theorem at_signed_adjacency (cash:(v.withIssuedSigned).SignedRoom floor w)
    (pre:PriorHeader.Room adj (v.area.H) (v.withIssuedSigned.signed).groups (v.withIssuedSigned.signed).lanes (v.prior.placement.degree) ((v.withIssuedSigned).donorEnd floor) w)
    (material:(v.withIssuedSigned).MaterialRoom ((v.withIssuedSigned).materialStart floor) parts (PriorHeader.reverseRank v.area.H v.withIssuedSigned.signed.groups v.withIssuedSigned.signed.lanes v.prior.placement.degree (v.withIssuedSigned.donorEnd floor)) w)
    (room:DescentOrdinaryVenueReturn.Room ((⟨count,input.roster,input.hubs⟩:DescentOrdinaryVenueReturn.Sources)) ((v.withIssuedSigned).materialEnd floor) (v.area.H) v.area.D v.venue.hosts v.venue.degree w)
    (mark:(v.withIssuedSigned).MarkRoom floor input w)
    (existing:∀h j,m (adj.base+h.val*(v.prior.placement.degree)+j.val)=(number (R h j):Computability.VPVNP.BurstRAM.Word w)):
    ∀h j,(v.signedReturn floor input count parts adj w).image m (adj.base+h.val*(v.prior.placement.degree)+j.val)=(number (R h j):Computability.VPVNP.BurstRAM.Word w):=by
  have issued:=PriorHeader.any (v.area.H) (v.withIssuedSigned.signed).groups (v.withIssuedSigned.signed).lanes (v.prior.placement.degree) ((v.withIssuedSigned).donorEnd floor) adj pre m
  have before:=(v.signed_predecessor_frames floor input count parts adj m material room mark).1
  have after:=(v.withIssuedSigned).signed_any floor w (v.issuedSignedChart) cash ((v.signedPredecessor floor input count parts adj w).image m)
  have left:(v.withIssuedSigned).donorEnd floor≤(v.withIssuedSigned).materialStart floor:=by
    rw [materialStart,PriorHeader.translated];exact Nat.le_add_right ..
  have right:(v.withIssuedSigned).donorEnd floor≤(v.withIssuedSigned).markEnd floor:=
    ((v.withIssuedSigned).signed_stage_paid floor).1.trans (((v.withIssuedSigned).signed_stage_paid floor).2.1.trans ((v.withIssuedSigned).markShape.low _))
  intro h j
  have headerOffsetBound:h.val*(v.prior.placement.degree)+j.val<(v.area.H)*(v.prior.placement.degree):=by
    have lt:=Nat.mul_le_mul_right (v.prior.placement.degree) (show h.val+1≤(v.area.H) from h.isLt)
    rw [Nat.add_mul,Nat.one_mul] at lt
    omega
  have low:=((Nat.add_lt_add_left (headerOffsetBound.trans_le pre.oldSize) adj.base).trans_le pre.old.2.2)
  rw [← Nat.add_assoc] at low
  exact (after.2 _ (.inl (low.trans_le right))).trans ((before _ (low.trans_le left)).trans
    ((issued.2 _ (.inl low)).trans (existing h j)))

theorem signed_original_panel (cash:(v.withIssuedSigned).SignedRoom floor w)
    (pre:PriorHeader.Room adj (v.area.H) (v.withIssuedSigned.signed).groups (v.withIssuedSigned.signed).lanes (v.prior.placement.degree) ((v.withIssuedSigned).donorEnd floor) w)
    (material:(v.withIssuedSigned).MaterialRoom ((v.withIssuedSigned).materialStart floor) parts (PriorHeader.reverseRank v.area.H v.withIssuedSigned.signed.groups v.withIssuedSigned.signed.lanes v.prior.placement.degree (v.withIssuedSigned.donorEnd floor)) w)
    (past:parts.base+parts.size≤(v.withIssuedSigned).donorEnd floor)
    (room:DescentOrdinaryVenueReturn.Room ((⟨count,input.roster,input.hubs⟩:DescentOrdinaryVenueReturn.Sources)) ((v.withIssuedSigned).materialEnd floor) (v.area.H) v.area.D v.venue.hosts v.venue.degree w)
    (mark:(v.withIssuedSigned).MarkRoom floor input w) :
    DescentPackedColony.Reads parts (fun h g=>DepotRAM.combine (v.ticket.depotShape v.short) (B.material h g)) (v.withIssuedSigned.material.oldLanes) ((v.signedReturn floor input count parts adj w).image m):=by
  have issued:=PriorHeader.any (v.area.H) (v.withIssuedSigned.signed).groups (v.withIssuedSigned.signed).lanes (v.prior.placement.degree) ((v.withIssuedSigned).donorEnd floor) adj pre m
  have before:=(v.signed_predecessor_frames floor input count parts adj m material room mark).1
  have after:=(v.withIssuedSigned).signed_any floor w (v.issuedSignedChart) cash ((v.signedPredecessor floor input count parts adj w).image m)
  have left:(v.withIssuedSigned).donorEnd floor≤(v.withIssuedSigned).materialStart floor:=by
    rw [materialStart,PriorHeader.translated];exact Nat.le_add_right ..
  have right:(v.withIssuedSigned).donorEnd floor≤(v.withIssuedSigned).markEnd floor:=
    ((v.withIssuedSigned).signed_stage_paid floor).1.trans (((v.withIssuedSigned).signed_stage_paid floor).2.1.trans ((v.withIssuedSigned).markShape.low _))
  intro t
  have low:parts.base+(row (v.area.H) (v.schedule.groupCount v.age) (v.withIssuedSigned.material.oldLanes) t).val<(v.withIssuedSigned).donorEnd floor:=
    (Nat.add_lt_add_left ((row (v.area.H) (v.schedule.groupCount v.age) (v.withIssuedSigned.material.oldLanes) t).isLt.trans_le material.sourceSize) parts.base).trans_le past
  exact (after.2 _ (.inl (low.trans_le right))).trans ((before _ (low.trans_le left)).trans
    ((issued.2 _ (.inl low)).trans (B.source t)))


include choiceEq age radix in
theorem registered_resolver_heads (cash:(phys).SignedRoom floor w)
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
    (pg:Fin (phys).vector.pageCount)
    (headerRoom:(phys).OperandHeaderRoom floor entry «matching» (entry.directory phys floor «matching»).refs
      ((entry.directory phys floor «matching»).refs pg) w)
    (panelAt:entry.venue.panel=parts) :
    let refs:=(entry.directory phys floor «matching»).refs
    let installed:=entry.mountedTape phys floor ((paid).image m)
    let gathered:=(refs.phase w ((phys).vectorStart floor)).image installed
    let mouth:=((phys).originAndMouth floor w entry «matching» (phys).operandShortBits (refs pg)).image gathered
    let here:=((phys).operandEarlyPhase floor w entry).image mouth
    let boot:=PriorHeader.image H (ss).groups (ss).lanes D ((phys).donorEnd floor) adj m
    let original:=((phys).materialAt ((phys).materialStart floor) parts ((phys).operandRanks floor).reverseRank w).image boot
    (∀a,a<(phys).material.endAddress ((phys).materialStart floor)→here a=original a) ∧
    (∀x j,DescentPackedZip.Source ((phys).parentSerial floor chart x j)
        (v.retainedSerial oldFit R selected m parts B choiceEq wide age radix cash.groups reciprocal x j) (ss).lanes here ∧
      DescentPackedZip.Source ((phys).parentPeer floor chart x j)
        (v.retainedPeer oldFit R selected m parts B choiceEq wide age radix cash.groups reciprocal x j) (ss).lanes here) ∧
    (∀h j,m (adj.base+h.val*D+j.val)=(number (R h j):Computability.VPVNP.BurstRAM.Word w)) ∧
    DescentPackedColony.Reads parts (fun h g=>DepotRAM.combine fmt (B.material h g)) M m ∧
    DescentPackedColony.Reads entry.venue.panel (fun h g=>DepotRAM.combine fmt (B.material h g)) M installed :=by
  intro refs installed gathered mouth here boot original
  have issued:=v.original_heads_at_headers (oldFit:=oldFit) (R:=R) (selected:=selected) (m:=m)
    (parts:=parts) (B:=B) (choiceEq:=choiceEq) (wide:=wide) (age:=age) (radix:=radix) (reciprocal:=reciprocal)
    (floor:=floor) (input:=input) (count:=count) (adj:=adj)
    cash pre material past existing room mark oldMarks newDegree matcher precision lower old wires countRead countLow
    place entry «matching» refs (refs pg) headerRoom
  refine ⟨issued.2,fun x j=>⟨(issued.1 x j).1.2,(issued.1 x j).2.2⟩,existing,B.source,?_⟩
  rw [panelAt]
  have posted:=v.signed_original_panel oldFit R selected m parts B floor input count adj cash pre material past room mark
  have toSigned : (phys).donorEnd floor≤(phys).signedEnd floor:=
    (((phys).signed_stage_paid floor).1.trans ((phys).signed_stage_paid floor).2.1).trans
      (((phys).markShape.low _).trans ((ss).room _))
  have toRefs : (phys).signedEnd floor≤(phys).refsStart floor:=Nat.le_add_right ..
  have vecRoom : (phys).vectorStart floor<2^w:=by
    have later:=(phys).ticket_source_order floor
    obtain ⟨r₁,r₂,r₃,r₄,r₅,r₆,_,_,_⟩:=later
    exact (((phys).vector_before floor).trans (r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans (r₆))))))).trans_lt headerRoom.ceiling
  have inlet:=entry.inlet_any phys floor headerRoom.inlet ((paid).image m)
  have chip:=entry.chip_fits phys floor headerRoom.inlet «matching»
  have mount:=(phys).mount_run floor (entry.chipBank phys floor) ((entry.inlet phys floor w).image ((paid).image m)) chip vecRoom
  intro t
  have low:parts.base+(row H J M t).val<(phys).donorEnd floor:=
    (Nat.add_lt_add_left ((row H J M t).isLt.trans_le material.sourceSize) _).trans_le past
  exact (mount.2.2.1 _ (.inl (low.trans_le (toSigned.trans toRefs)))).trans
    ((inlet.2 _ (.inl (low.trans_le toSigned))).trans (posted t))

include choiceEq age radix in
theorem original_resolver_keys (cash:(phys).SignedRoom floor w)
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
    (shape:(phys).VectorShape) (blocks:(phys).resolver.blocks=(phys).material.blocks)
    (bound:(phys).resolver.hosts≤(phys).material.hosts) (groups:(phys).resolver.groups=(phys).material.groups)
    {nb mb:ℕ} (pg:Fin (phys).vector.pageCount)
    (headerRoom:(phys).OperandHeaderRoom floor entry «matching» (entry.directory phys floor «matching»).refs
      ((entry.directory phys floor «matching»).refs pg) w)
    (panelAt:entry.venue.panel=parts)
    (chip:Fin (phys).bornBook.hosts→Fin (phys).bornBook.groups→Cell (phys).bornBook.chipBits)
    (oldBooks:References.Rows (phys).vector (phys).reference.degree (phys).reference.k (phys).reference.oldNodes
      (phys).reference.capacity ((phys).resolver.size+2) nb mb)
    (low : Fin (phys).vector.lows) (hostGeometry : (phys).vector.hosts=(phys).material.oldHosts)
    (pathGeometry : breadth (phys).reference.degree=paths)
    (walkGeometry : HEq (oldBooks pg low).walks (Gather.reaching R))
    (homes:(phys).bornBook.hosts=(phys).vector.hosts) (gs:(phys).bornBook.groups=(phys).vector.groups*(phys).vector.radix)
    (bits:(phys).bornBook.bits=(phys).resolver.size+2)
    (admit:(phys).TicketAdmission floor w chart entry «matching» pg)
    (data:DescentPackedColony.Reads (entry.chipBank phys floor) chip (phys).bornBook.lanes (entry.mountedTape phys floor ((paid).image m)))
    (span:(phys).bornBook.rows≤(entry.chipBank phys floor).size)
    (lane:(phys).bornBook.lanes=(phys).vector.lanes*(phys).vector.radix)
    (bookWidth:(phys).vector.bookBits=((phys).resolver.size+2)*(phys).resolver.nodes)
    (pages:∀p q,ScalarOperand.Measured (((entry.directory phys floor «matching»).refs p) q) (oldBooks p q)
      (phys).resolver.nodes ((phys).vector.lanes*(phys).vector.radix) ((phys).vectorStart floor)
      (entry.mountedTape phys floor ((paid).image m)))
    (purchased:(phys).origin.preparationWords=(phys).originControlWords+(phys).originMouthWords+(phys).rootSourceSize)
    (full:(phys).endAddress floor<2^w) (operandWidth:(phys).resolver.lanes*DescentPackedOperand.unit (phys).resolver.size≤w/2)
    (typed:BookPointers (fun x p=>previousValues (phys).resolver (phys).vector shape.operands shape.blocks
      shape.hosts shape.groups (References.returnedValue (phys).vector oldBooks (phys).resolver.nodes) p x))
    (limit:22*(fmt).cap+10<2^((phys).resolver.size+2)) :
    let installed:=entry.mountedTape phys floor ((paid).image m)
    let refs:=(entry.directory phys floor «matching»).refs
    let serial:=v.retainedSerial oldFit R selected m parts B choiceEq wide age radix cash.groups reciprocal
    let peer:=v.retainedPeer oldFit R selected m parts B choiceEq wide age radix cash.groups reciprocal
    let prev:=fun j f h k=>ScalarOperand.take (((phys).resolver.index.symm j).2.1)
      ((phys).previousHeaderValue shape oldBooks j f h k)
    let lastRows:=(phys).headerMouthRows floor entry «matching» oldBooks homes gs bits
    let born:=fun j f h k=>ScalarOperand.take (((phys).resolver.index.symm j).2.1)
      ((phys).mouthHeaderValue floor entry «matching» shape lastRows chip homes gs j f h k)
    let origin:=(phys).originHeaderValue shape (oldBooks pg)
    let heads:=(phys).sampleHeads blocks bound groups origin prev born
      ((phys).wideMaterialValues R B.material cash.groups serial peer) ((phys).narrowValue R)
    let words:=ticketAt (phys).ticketReadGeometry (DescentDatedOperandReadPipeline.SortedInput.values (phys).ticketReadGeometry
      ((phys).originalValues heads) ((phys).walkValues (Gather.reaching R)))
    let prevPages:=fun x p=>previousValues (phys).resolver (phys).vector shape.operands shape.blocks shape.hosts shape.groups
      (References.returnedValue (phys).vector oldBooks (phys).resolver.nodes) p x
    let digits:=fun j h k=>(phys).matched_role_room R B.material cash.groups serial peer blocks bound groups origin prev born j h k
      ((phys).raw_role_room floor entry «matching» shape pg oldBooks chip homes gs bits installed
        (Nat.mul_pos admit.lanes admit.radix) pages j h k) limit
    let raw:=ofBooks prevPages typed (fun j h k=>DescentDatedPublicGrain.withGrain (phys).chosenGrain ((phys).ticketSides words j h k))
      ((phys).ticketRoles words) digits
    ∀j,DescentPackedColony.Reads (Banks.wordBank (phys).resolver ((phys).normalizedEnd floor) j)
      (fun h k=>DescentPackedOperand.word ((raw j).compiled h k)) (phys).resolver.lanes
      (((phys).routedArguments floor refs ((phys).nativeTicketExpr floor chart entry «matching» shape blocks)
        ((phys).nativeTicketPreparation floor w chart entry «matching» shape blocks pg) shape full operandWidth).image installed) :=by
  obtain ⟨saved,parents,neighbor,original,panel⟩:=v.registered_resolver_heads (oldFit:=oldFit) (R:=R)
    (selected:=selected) (m:=m) (parts:=parts) (B:=B) (choiceEq:=choiceEq) (wide:=wide)
    (age:=age) (radix:=radix) (reciprocal:=reciprocal) (floor:=floor) (input:=input) (count:=count) (adj:=adj)
    cash pre material past existing room mark oldMarks newDegree matcher precision lower old wires countRead countLow
    place entry «matching» pg headerRoom panelAt
  have toSigned : (phys).donorEnd floor≤(phys).signedEnd floor:=
    (((phys).signed_stage_paid floor).1.trans ((phys).signed_stage_paid floor).2.1).trans
      (((phys).markShape.low _).trans ((ss).room _))
  have toRefs : (phys).signedEnd floor≤(phys).refsStart floor:=Nat.le_add_right ..
  have fullOrder:=(phys).mount_order floor
  have earlier:entry.venue.panel.base+entry.venue.panel.size≤(phys).vectorStart floor:=by
    rw [panelAt]
    exact past.trans (toSigned.trans (toRefs.trans (fullOrder.1.trans fullOrder.2)))
  have chipFit:=entry.chip_fits phys floor headerRoom.inlet «matching»
  have walks:=(phys).registered_walk_banks floor entry «matching» pg low headerRoom adj parts m ((paid).image m)
    pre chart material R neighbor saved (oldBooks pg low) (pages pg low) hostGeometry pathGeometry walkGeometry
  exact (phys).registered_resolver_keys floor chart entry «matching» shape blocks bound groups pg chip oldBooks homes gs bits
    R B.material cash.groups _ _ adj parts m (entry.mountedTape phys floor ((paid).image m)) cash admit pre material neighbor
    original past saved walks parents B.live panel earlier headerRoom.gather (Chooser.bank_before chipFit (fullOrder.1.trans fullOrder.2))
    span data lane bookWidth pages purchased full operandWidth typed limit

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
