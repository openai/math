import OAI.Hierarchy.DescentDatedSignedParentValues
import OAI.Hierarchy.DescentDatedSignedParentHeads
import OAI.Hierarchy.DescentDatedSignedNewNeighbors
import OAI.Hierarchy.DescentDatedOriginalLaunchSites
import OAI.Hierarchy.DescentDatedSignedAfterMark
import OAI.Hierarchy.DescentDatedSignedLaunchSource
import OAI.Hierarchy.DescentDatedOrdinarySignedPhysical
import OAI.Hierarchy.DescentDatedSignedAny

namespace OAI
/-! Physical read of every signed output from the original donor board, adjacency, and matched material date. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open DescentHaloWalkRAM DescentHaloPackedRebase DescentPackedColony DescentSIMDLookup DescentRawCablePanel
open DescentPackedChildNeighbor DescentPacking.PackedMatch.Local DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F Pin E X T V : Type} [Field F] [Fintype E] [Fintype X] [Fintype T] (v : PhysicalOrdinary F Pin)
local notation "phys" => v.withIssuedSigned
local notation "s₀" => (phys).signed
local notation "c₀" => v.issuedSignedChart
local notation "A₁" => v.target.placement
local notation "native" => v.target.order.trans Fin.valEmbedding
local notation "group" => (Function.Embedding.refl (Fin (v.schedule.groupCount (v.age+1))))
local notation "H" => v.area.H
local notation "D" => v.prior.placement.degree
local notation "fmt" => (phys).ticket.depotShape (phys).short
local notation "M" => (s₀).lanes
local notation "J" => (s₀).groups
local notation "P₀" => (s₀).reach
variable (wide : Fintype.card v.target.V ≤ v.withIssuedSigned.signed.hosts)
local notation "host" => v.target.vertex.trans (Fin.castLEEmb wide)
local notation "who" => SignedExtent.wholeHost group host
local notation "near" => DescentPacking.PackedMatch.Local.Stage.hostRotor host (DescentGroupPeerOrder.hostRoster A₁ ((host).trans Fin.valEmbedding))
variable (C : Blocks (Stage.source v.target.placement (v.target.order.trans Fin.valEmbedding)) E) (marked : E→Prop)
    (R : Fin v.area.H→Fin v.prior.placement.degree→Option (Fin v.area.H))
    (symm : ∀a b j,R a j=some b→∃l,R b l=some a)
    (Z : Measured C R X T V v.withIssuedSigned.signed.lowSites v.withIssuedSigned.signed.residentSlots v.withIssuedSigned.signed.tickets v.withIssuedSigned.signed.cap) (shelf : Measured.Shelf C R Z)
local notation "small" => fun h path x (a : ParentFilter.Source P₀ (s₀).lowSites (s₀).tickets (s₀).cap) f =>
  Fused.field_room R (Z.venue h) path (Z.loc x).1 a f v.signedLayout.field_room.1
local notation "raw" => fun (z:(s₀).Socket)=>Fused.cell C R Z shelf small (who z.1) z.2
local notation "here" => Measured.roster C R symm Z
local notation "srcFace" e:arg => (⟨(e).val,(e).property.1,Or.inl rfl⟩ : Local C (C.src (e).val))
variable (floor : ℕ) (input : Stage.Dated.Operands) (count parts adj : Bank) {w : ℕ} (m : Memory w)
local notation "I₀" => (phys).signedInput floor c₀
local notation "mat" => (phys).materialStart floor
local notation "base" => (phys).markEnd floor
local notation "directory" => PriorHeader.reverseRank H J M D ((phys).donorEnd floor)
local notation "sources" => (⟨count,input.roster,input.hubs⟩ : DescentOrdinaryVenueReturn.Sources)
local notation "out" => NativePhase.image (v.signedPredecessor floor input count parts adj w) m
variable (state : Fin v.area.H→Fin v.withIssuedSigned.material.oldGroups→DepotRAM.Parts (v.withIssuedSigned.ticket.depotShape v.withIssuedSigned.short))
variable (cash : v.withIssuedSigned.SignedRoom floor w)
variable (pr : ∀h g z,DepotRAM.Material.ParentRoom (v.withIssuedSigned.ticket.depotShape v.withIssuedSigned.short) v.withIssuedSigned.materialFormat (state h g)
  (digest (DepotRAM.Material.reverseEntries (v.withIssuedSigned.ticket.depotShape v.withIssuedSigned.short) R h)) z v.withIssuedSigned.signed.lowSites v.withIssuedSigned.signed.tickets v.withIssuedSigned.signed.cap)
local notation "pitch" => (phys).materialPitch
local notation "parent" x:arg o:arg h:arg g:arg => (phys).originalParent R state cash.groups pr ((c₀).donorSeat o) h (finProdFinEquiv (g,x))
variable (positive : 0<v.withIssuedSigned.materialPitch) (inside : v.withIssuedSigned.materialPitch≤v.withIssuedSigned.signed.lowSites)
local notation "arrived" => (phys).signedIncoming c₀ rfl R state cash.groups v.signedLayout.field_room.1 positive inside pr
local notation "earlier₀" => (phys).originalDigits c₀ rfl cash.groups R state

theorem signed_measured_heads (pre : PriorHeader.Room adj H J M D ((phys).donorEnd floor) w)
    (matRoom : (phys).MaterialRoom mat parts directory w) (past : parts.base+parts.size≤(phys).donorEnd floor)
    (data : Reads parts (fun h g=>DepotRAM.combine fmt (state h g)) (phys).material.oldLanes m)
    (income : ∀h j,m (adj.base+h.val*D+j.val)=(number (R h j):Word w))
    (venue : DescentOrdinaryVenueReturn.Room sources ((phys).materialEnd floor) H v.area.D v.venue.hosts v.venue.degree w)
    (mark : (phys).MarkRoom floor input w) (priorLanes : 0<(phys).material.oldLanes)
    (sites : DepotRAM.Material.Route.Projection.launchSites (phys).material.blocks pitch=(s₀).lowSites)
    (newDegree : v.venue.degree=(A₁).degree)
    (neighbors : ∀h j,out ((I₀).newNeighbors.base+(h.val*(A₁).degree+j.val))=(number (near h j):Word w))
    (emission : DescentResetWindowFields.Emission A₁ native C marked)
    (orders : ∀h (e f:Local C h),DescentParallelBase.Incidence.srcKey C R symm Z h e<
      DescentParallelBase.Incidence.srcKey C R symm Z h f ↔ Z.site (Z.src (Z.head h e))<Z.site (Z.src (Z.head h f)))
    (coord : ∀u,(host u.1.2).val=(Z.venue u).1.val*pitch+(Z.venue u).2.val)
    (low : ∀u,(Z.venue u).2.val<pitch)
    (same : ∀u (e:Local C u),Z.loc (Z.raw u e)=Z.loc (Z.raw (C.src e.val) (srcFace e)))
    (trace : ∀z,arrived z=raw z)
    (launch : ∀x h g t,who x h g=some t→∀e:Local C t,
      let a:=Z.loc (Z.raw t e); parent x a.2 a.1 g=some (Z.read (C.src e.val) (srcFace e)))
    (mb : Fin (2^v.k)→Fin (P₀*(s₀).residentSlots)→Fin (s₀).hosts→Fin J→Cell 1)
    (flag : ∀x j,((I₀).mark (x,j)).Fits w base ∧ Source ((I₀).mark (x,j)) (mb x j) M out)
    (markedAt : ∀x j h g u,who x h g=some u→∀e:Local C u,(here).address u e=j→((mb x j h g).val=1 ↔ marked e.val)) :
    ((∀x axis j,let field:=(s₀).retainedRankField base x axis j
        field.Fits w ((phys).signedEnd floor) ∧ Source field
          (fun h g=>(DescentOrdinarySignedRanks.result C (Incidence.of_measured C R symm Z orders)
            who (Stage.measured A₁ native v.schedule v.target.valid) x axis j h g : Cell (s₀).fieldBits)) M
          (((phys).signedPhase floor c₀ w).image out)) ∧
      (∀x j,let field:=(s₀).peerField I₀ base (x,j)
        field.Fits w ((phys).signedEnd floor) ∧ Source field
          (SignedExtent.signedPeer (b:=(s₀).fieldBits) A₁ native v.schedule v.target.valid
            (DescentPacking.PackedMatch.Local.Stage.cableNames v.k (DescentStageEdgeReceipt.groupRank ((group).trans Fin.valEmbedding) ((host).trans Fin.valEmbedding))) C R symm Z who x j) M
          (((phys).signedPhase floor c₀ w).image out))) ∧
    ((phys).signedPhase floor c₀ w).Runs out ∧
    (∀x j,Reads ((s₀).page base x j) (fun h g=>DescentSignedCableCodec.encode
      (DescentPacking.PackedMatch.Local.Stage.Prepare.signed A₁ native v.schedule v.target.valid group host x j h g)) M (((phys).signedPhase floor c₀ w).image out)) ∧
    (∀a,a<base ∨ (phys).signedEnd floor≤a→((phys).signedPhase floor c₀ w).image out a=out a) ∧
    CheapCode ((phys).signedPhase floor c₀ w).program := by
  have book:=v.signed_history floor input count parts adj m R pre matRoom venue mark income
  have keep:=(v.signed_predecessor_frames floor input count parts adj m matRoom venue mark).2.1
  have prior:=(phys).signed_parent_run floor c₀ rfl R state cash.groups v.signedLayout.field_room.1 positive inside pr
    parts adj pre matRoom past priorLanes cash.lanes cash.blocks cash.growth m out income data base cash.material keep
  have sameRaw : arrived=raw := funext trace
  rw [sameRaw] at prior
  have origin:=(phys).original_earlier floor c₀ rfl sites cash.groups R state parts adj pre matRoom past
    priorLanes cash.lanes cash.blocks cash.growth m out income data keep
  have widths:=v.signedLayout.field_room
  have many : P₀*P₀<2^(s₀).fieldBits := by
    have rc:=widths.1
    change Fused.capacity D (s₀).lowSites (s₀).tickets (s₀).cap≤2^(s₀).fieldBits at rc
    have qp:0<(s₀).lowSites:=positive.trans_le inside
    change breadth D * breadth D < _
    have expand:=Nat.le_mul_of_pos_right (breadth D * breadth D) qp
    unfold Fused.capacity at rc
    omega
  apply SignedExtent.phase_from_hosts_heads A₁ native v.schedule v.target.valid C marked R symm Z shelf small orders group host
    (I₀) base out ((phys).signed_prior_sources floor w c₀ cash) cash.room ((phys).signed_peer_inputs floor w c₀ cash)
    many newDegree emission book.directory prior earlier₀ origin coord low same ?_ ?_
    ((phys).original_tokens c₀ rfl cash.groups R state) ((phys).original_back c₀ rfl cash.groups R state)
    book.ports book.reverse book.ranked book.endpoints neighbors mb (fun x j=>(flag x j).2) (fun z=>(flag z.1 z.2).1)
    markedAt widths.2.1 widths.2.2.1 widths.2.2.2.1
  · intro x h g t got e
    exact (phys).original_forward c₀ rfl cash.groups R state pr _ _ _ _ _ (launch x h g t got e) widths.1
  · intro x h g t got e
    exact ((phys).original_low c₀ rfl cash.groups R state pr _ _ _ _ _ (launch x h g t got e) widths.1).trans
      (congrArg Fin.val (Z.reached (C.src e.val) (srcFace e)).srcLow)
theorem signed_measured_run (pre : PriorHeader.Room adj H J M D ((phys).donorEnd floor) w)
    (matRoom : (phys).MaterialRoom mat parts directory w) (past : parts.base+parts.size≤(phys).donorEnd floor)
    (data : Reads parts (fun h g=>DepotRAM.combine fmt (state h g)) (phys).material.oldLanes m)
    (income : ∀h j,m (adj.base+h.val*D+j.val)=(number (R h j):Word w))
    (venue : DescentOrdinaryVenueReturn.Room sources ((phys).materialEnd floor) H v.area.D v.venue.hosts v.venue.degree w)
    (mark : (phys).MarkRoom floor input w) (priorLanes : 0<(phys).material.oldLanes)
    (sites : DepotRAM.Material.Route.Projection.launchSites (phys).material.blocks pitch=(s₀).lowSites)
    (newDegree : v.venue.degree=(A₁).degree)
    (neighbors : ∀h j,out ((I₀).newNeighbors.base+(h.val*(A₁).degree+j.val))=(number (near h j):Word w))
    (emission : DescentResetWindowFields.Emission A₁ native C marked)
    (orders : ∀h (e f:Local C h),DescentParallelBase.Incidence.srcKey C R symm Z h e<
      DescentParallelBase.Incidence.srcKey C R symm Z h f ↔ Z.site (Z.src (Z.head h e))<Z.site (Z.src (Z.head h f)))
    (coord : ∀u,(host u.1.2).val=(Z.venue u).1.val*pitch+(Z.venue u).2.val)
    (low : ∀u,(Z.venue u).2.val<pitch)
    (same : ∀u (e:Local C u),Z.loc (Z.raw u e)=Z.loc (Z.raw (C.src e.val) (srcFace e)))
    (trace : ∀z,arrived z=raw z)
    (launch : ∀x h g t,who x h g=some t→∀e:Local C t,
      let a:=Z.loc (Z.raw t e); parent x a.2 a.1 g=some (Z.read (C.src e.val) (srcFace e)))
    (mb : Fin (2^v.k)→Fin (P₀*(s₀).residentSlots)→Fin (s₀).hosts→Fin J→Cell 1)
    (flag : ∀x j,((I₀).mark (x,j)).Fits w base ∧ Source ((I₀).mark (x,j)) (mb x j) M out)
    (markedAt : ∀x j h g u,who x h g=some u→∀e:Local C u,(here).address u e=j→((mb x j h g).val=1 ↔ marked e.val)) :
    ((phys).signedPhase floor c₀ w).Runs out ∧
    (∀x j,Reads ((s₀).page base x j) (fun h g=>DescentSignedCableCodec.encode
      (DescentPacking.PackedMatch.Local.Stage.Prepare.signed A₁ native v.schedule v.target.valid group host x j h g)) M (((phys).signedPhase floor c₀ w).image out)) ∧
    (∀a,a<base ∨ (phys).signedEnd floor≤a→((phys).signedPhase floor c₀ w).image out a=out a) ∧
    CheapCode ((phys).signedPhase floor c₀ w).program  :=by
  exact (v.signed_measured_heads wide C marked R symm Z shelf floor input count parts adj m state cash pr positive inside
    pre matRoom past data income venue mark priorLanes sites newDegree neighbors emission orders coord low same trace launch
    mb flag markedAt).2

variable (oldFit:Fintype.card v.prior.V≤v.area.H)
local notation "mb₀" => (phys).markBits c₀ oldFit cash.groups.symm R
local notation "roleRows" => fun (x:Fin (2^v.k)) (j:Fin (P₀*(s₀).residentSlots))=>arrived (x,j)
local notation "sourceRows" => fun (x:Fin (2^v.k)) (j:Fin (s₀).residentSlots) (h:Fin (s₀).priorHosts) (g:Fin J)=>parent x j h g

/-- Consume the earlier original graph drawing on the registered donor board and
return the actual signed bank used by the following ordinary or reset date. -/
theorem signed_drawing_heads (d:SignedDrawing A₁ native R symm host pitch
      v.signedLayout.field_room.1 roleRows sourceRows mb₀)
    (pre:PriorHeader.Room adj H J M D ((phys).donorEnd floor) w)
    (matRoom:(phys).MaterialRoom mat parts directory w) (past:parts.base+parts.size≤(phys).donorEnd floor)
    (data:Reads parts (fun h g=>DepotRAM.combine fmt (state h g)) (phys).material.oldLanes m)
    (income:∀h j,m (adj.base+h.val*D+j.val)=(number (R h j):Word w))
    (venue:DescentOrdinaryVenueReturn.Room sources ((phys).materialEnd floor) H v.area.D v.venue.hosts v.venue.degree w)
    (mark:(phys).MarkRoom floor input w) (priorLanes:0<(phys).material.oldLanes) (oldMarks:0<(phys).markShape.oldLanes)
    (newDegree:v.venue.degree=(A₁).degree) (matcher:v.area.Space input w floor)
    (precision lower:ℕ) (old:stageVenue v.prior oldFit input (phys).markShape.oldLanes precision lower
      (v.prior.venueRoster oldFit) m)
    (wires:∀(x:Fin (2^v.k))(j:Fin (2*v.prior.placement.cap)),
      (input.wire x.val j.val).base+H*chunks (v.schedule.groupCount v.age) (phys).markShape.oldLanes≤lower)
    (countRead:m count.base=(Fintype.card v.prior.V:Word w)) (countLow:count.base<lower)
    (place:lower≤(phys).donorEnd floor) :
    (∀x j,let x':=x.cast (c₀).blocks.symm
      let j':=(phys).parentSlot c₀ j
      (((phys).parentSerial floor c₀ x j).Fits w ((phys).signedEnd floor) ∧
        Source ((phys).parentSerial floor c₀ x j) (d.serial v.schedule v.target.valid x' j') M (((phys).signedPhase floor c₀ w).image out)) ∧
      (((phys).parentPeer floor c₀ x j).Fits w ((phys).signedEnd floor) ∧
        Source ((phys).parentPeer floor c₀ x j) (d.peer v.schedule v.target.valid x' j') M (((phys).signedPhase floor c₀ w).image out))) ∧
    ((phys).signedPhase floor c₀ w).Runs out ∧
    (∀x j,Reads ((s₀).page base x j) (fun h g=>DescentSignedCableCodec.encode
      (DescentPacking.PackedMatch.Local.Stage.Prepare.signed A₁ native v.schedule v.target.valid group host x j h g)) M (((phys).signedPhase floor c₀ w).image out)) ∧
    (∀a,a<base ∨ (phys).signedEnd floor≤a→((phys).signedPhase floor c₀ w).image out a=out a) ∧
    CheapCode ((phys).signedPhase floor c₀ w).program :=by
  let:=d.finiteEdge
  let:=d.finiteRaw
  let:=d.finiteTicket
  have after:=v.signed_neighbors floor input count parts adj m oldFit wide old wires countRead countLow place
    pre matRoom venue mark v.prior.branch (newDegree.trans v.target.branch)
  have startBound:base<2^w:=((s₀).room base).trans_lt ((Nat.le_add_right ..).trans_lt cash.room)
  have flags:=(phys).signed_mark_after_hosts floor input count parts adj c₀ oldFit cash.groups.symm m oldMarks cash.lanes
    cash.blocks pre matRoom venue startBound matcher precision lower (v.prior.venueRoster oldFit) old R income
  have all:=v.signed_measured_heads wide d.blocks d.core R symm d.observed d.shelf floor input count parts adj m state cash
    pr positive inside pre matRoom past data income venue mark priorLanes v.issued_launch_sites newDegree after d.emission
    d.order d.coordinate d.low d.address (fun z=>d.input z.1 z.2) d.launch mb₀ flags d.mark
  exact ⟨fun x j=>⟨all.1.1 (x.cast (c₀).blocks.symm) 1 ((phys).parentSlot c₀ j),
    all.1.2 (x.cast (c₀).blocks.symm) ((phys).parentSlot c₀ j)⟩,all.2⟩

theorem signed_drawing_run (drawing:Nonempty (SignedDrawing A₁ native R symm host pitch
      v.signedLayout.field_room.1 roleRows sourceRows mb₀))
    (pre:PriorHeader.Room adj H J M D ((phys).donorEnd floor) w)
    (matRoom:(phys).MaterialRoom mat parts directory w) (past:parts.base+parts.size≤(phys).donorEnd floor)
    (data:Reads parts (fun h g=>DepotRAM.combine fmt (state h g)) (phys).material.oldLanes m)
    (income:∀h j,m (adj.base+h.val*D+j.val)=(number (R h j):Word w))
    (venue:DescentOrdinaryVenueReturn.Room sources ((phys).materialEnd floor) H v.area.D v.venue.hosts v.venue.degree w)
    (mark:(phys).MarkRoom floor input w) (priorLanes:0<(phys).material.oldLanes) (oldMarks:0<(phys).markShape.oldLanes)
    (newDegree:v.venue.degree=(A₁).degree) (matcher:v.area.Space input w floor)
    (precision lower:ℕ) (old:stageVenue v.prior oldFit input (phys).markShape.oldLanes precision lower
      (v.prior.venueRoster oldFit) m)
    (wires:∀(x:Fin (2^v.k))(j:Fin (2*v.prior.placement.cap)),
      (input.wire x.val j.val).base+H*chunks (v.schedule.groupCount v.age) (phys).markShape.oldLanes≤lower)
    (countRead:m count.base=(Fintype.card v.prior.V:Word w)) (countLow:count.base<lower)
    (place:lower≤(phys).donorEnd floor) :
    ((phys).signedPhase floor c₀ w).Runs out ∧
    (∀x j,Reads ((s₀).page base x j) (fun h g=>DescentSignedCableCodec.encode
      (DescentPacking.PackedMatch.Local.Stage.Prepare.signed A₁ native v.schedule v.target.valid group host x j h g)) M (((phys).signedPhase floor c₀ w).image out)) ∧
    (∀a,a<base ∨ (phys).signedEnd floor≤a→((phys).signedPhase floor c₀ w).image out a=out a) ∧
    CheapCode ((phys).signedPhase floor c₀ w).program  :=by
  obtain ⟨d⟩:=drawing
  exact (v.signed_drawing_heads (wide:=wide) (R:=R) (symm:=symm) (floor:=floor) (input:=input)
    (count:=count) (parts:=parts) (adj:=adj) (m:=m) (state:=state) (cash:=cash) (pr:=pr)
    (positive:=positive) (inside:=inside) (oldFit:=oldFit) d pre matRoom past data income venue mark priorLanes
    oldMarks newDegree matcher precision lower old wires countRead countLow place).2
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
