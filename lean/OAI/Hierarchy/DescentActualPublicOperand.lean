import OAI.Hierarchy.DescentDatedOriginalIncoming
import OAI.Hierarchy.DescentOrdinaryRawEmittedOperand
import OAI.Hierarchy.DescentReachedTransportPublic
import OAI.Hierarchy.DescentDatedSignedCapacity

namespace OAI
/-! The native public argument after the two original quotients and naming. -/
namespace Hierarchy.DescentDatedAddressBook.SignedDrawing
open DescentSixParty DescentOrdinarySignedRanks DescentOrdinarySignedMeta DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open DescentHaloWalkRAM DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F Pin U : Type} [Field F] [Fintype U] [DecidableEq U]
  {d H prior degree Q O K L b groups k age : ℕ} {bits : Pin→ℕ} {W:MarkedWorld F d Pin bits}
  {G:PoweredGadget F} {price ε:ℝ} {A:GroupStage W G price ε (Fin groups) U k}
  {native:W.graph.Edge↪ℕ} {R:Fin prior→Fin degree→Option (Fin prior)}
  {symm:∀u v j,R u j=some v→∃n,R v n=some u} {host:U↪Fin H} {pitch:ℕ}
  {space:Fused.capacity degree Q K L≤2^b}
  {before:Fin (2^k)→Fin (breadth degree*O)→Fin H→Fin groups→Option (Fused.Raw R Q K L b)}
  {parent:Fin (2^k)→Fin O→Fin prior→Fin groups→Option (ParentFilter.Source (breadth degree) Q K L)}
  {marks:Fin (2^k)→Fin (breadth degree*O)→Fin H→Fin groups→Cell 1}
variable (d₀:SignedDrawing A native R symm host pitch space before parent marks)
    (S:DescentCompiler.AtomSchedule) (ready:A.StateBounds S age)
local notation "group" => (Function.Embedding.refl (Fin groups))
local notation "home" => SignedExtent.wholeHost group host
local notation "name" => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (DescentStageEdgeReceipt.groupRank ((group).trans Fin.valEmbedding) (host.trans Fin.valEmbedding))

local instance physicalOperandDrawingEdgeFintype : Fintype d₀.edge := d₀.finiteEdge
local instance physicalOperandDrawingRawFintype : Fintype d₀.raw := d₀.finiteRaw
local instance physicalOperandDrawingTicketFintype : Fintype d₀.ticket := d₀.finiteTicket

local notation "RR" => Measured.roster d₀.blocks R symm d₀.observed
local notation "slot" h:arg e:arg => (RR).address h e
local notation "Z₀" => Incidence.of_measured d₀.blocks R symm d₀.observed d₀.order


open DescentPackedOperand DescentResetWindowFields
local notation "atChild" side:arg e:arg n:arg => Public.endpoint A native S ready name side (d₀.emission.units ⟨e,n⟩)


open DescentKernelHistory DescentBundleHistory DescentOperandStateBanks Computability.BorderVNP.Crossing
local notation "endpoint₀" => Public.endpoint A native S ready name

private theorem drawnFirstPointer (capacity : A.cap=L) (e : d₀.edge) (side : Bool) (child : Fin (d₀.blocks.count e))
    (wireFit : A.cap≤2^b) (peerFit : A.degree≤2^b) {wordBits : ℕ}
    (wireWide : A.cap≤2^(wordBits+2)) (peerWide : A.degree≤2^(wordBits+2))
    (chunk grain : Cell (wordBits+2)) (offset : d₀.core e → chunk.val/grain.val=child.val) :
    let h:=if side then d₀.blocks.dst e else d₀.blocks.src e
    let edge : Local d₀.blocks h := ⟨e,Nat.zero_lt_of_lt child.isLt,by cases side <;> simp [h]⟩
    let j:=(RR).address h edge
    let t:=d₀.emission.units ⟨e,child⟩
    let start : DescentSharedCableNames.Stage.Grain A := ⟨t.1,⟨0,Nat.zero_lt_of_lt t.2.isLt⟩⟩
    Pointer.ofKey 0 (resolve (Public.fragment (decide (d₀.core e))
      (d₀.digits S ready capacity h.2 j (host h.1.2) h.1.1).1
      (d₀.digits S ready capacity h.2 j (host h.1.2) h.1.1).2 chunk grain)) =
      .cable (endpoint₀ side start).neighbor.val (endpoint₀ side start).wire.val
        (if d₀.core e then chunk.val%grain.val else chunk.val) := by
  have get := d₀.budgeted_operand S ready capacity e side child wireFit peerFit wireWide peerWide chunk grain offset
  obtain ⟨near,beginAt⟩ := first_signed_fields A native S ready name d₀.blocks d₀.core d₀.emission e child side
  dsimp only
  rw [get]
  change Pointer.cable ((atChild side e child).neighbor.val) ((atChild side e child).wire.val - (atChild side e child).within.val) _=_
  rw [near,beginAt]
  by_cases active : d₀.core e <;> simp [active]


private theorem endpoint_incidence {U : Type} (src dst : U) (side : Bool) :
    src = (if side then dst else src) ∨ dst = (if side then dst else src) := by
  cases side <;> simp

private abbrev blockPointerResult (capacity : A.cap=L) (root : d₀.edge) {p : ℕ} (v : W.graph.Site)
    (observed : BlockRef p (boundaryWidth W.graph v) → Prop) (chunk grain : ℕ) {wordBits : ℕ}
    (bitsIn cut : Cell (wordBits+2)) : Prop :=
    ∃ edge : Incident W.graph v, ∃ low : ℕ, ∃ fits : (low+1)*p≤W.graph.width edge.val,
    observed ⟨.inl edge,low,fits⟩ ∧ ∃ child : Fin (d₀.blocks.count root),
    let unit₁:=d₀.emission.units ⟨root,child⟩
    let start : DescentSharedCableNames.Stage.Grain A:=⟨unit₁.1,⟨0,Nat.zero_lt_of_lt unit₁.2.isLt⟩⟩
    let side:=decide (W.graph.src edge.val≠v)
    let h:=if side then d₀.blocks.dst root else d₀.blocks.src root
    let edgeAt : Local d₀.blocks h:=⟨root,Nat.zero_lt_of_lt child.isLt,endpoint_incidence _ _ side⟩
    let slot₀:=(RR).address h edgeAt
    unit₁.1=edge.val ∧ child.val=chunk/grain ∧
    Pointer.ofKey 0 (resolve (Public.fragment (decide (d₀.core root))
      (d₀.digits S ready capacity h.2 slot₀ (host h.1.2) h.1.1).1
      (d₀.digits S ready capacity h.2 slot₀ (host h.1.2) h.1.1).2 bitsIn cut))=
      .cable (endpoint₀ side start).neighbor.val (endpoint₀ side start).wire.val low

private theorem observedBlockPointer (capacity : A.cap=L) (root : d₀.edge) {p : ℕ} (v : W.graph.Site)
    (observed : BlockRef p (boundaryWidth W.graph v) → Prop) (chunk grain : ℕ)
    (published : ∃ w : BlockRef p (boundaryWidth W.graph v), ∃ child : Fin (d₀.blocks.count root),
      observed w ∧ child.val=chunk/grain ∧
      let sent := d₀.emission.units ⟨root,child⟩
      w.cableNumber W.graph v = some (sent.1,if d₀.core root then chunk%grain else chunk) ∧
      sent.2.val=(if d₀.core root then 0 else child.val))
    (wireFit : A.cap≤2^b) (peerFit : A.degree≤2^b) {wordBits : ℕ}
    (wireWide : A.cap≤2^(wordBits+2)) (peerWide : A.degree≤2^(wordBits+2))
    (bitsIn cut : Cell (wordBits+2)) (bitsRead : bitsIn.val=chunk) (cutRead : cut.val=grain) :
    blockPointerResult d₀ S ready capacity root v observed chunk grain bitsIn cut := by
  obtain ⟨w,t,seen,idx,address,_⟩ := published
  rcases w with ⟨edge|pin,lo,cableRoom⟩
  · have sides := Prod.mk.inj (Option.some.inj address)
    refine ⟨edge,lo,cableRoom,seen,t,sides.1.symm,idx,?_⟩
    let side := decide (W.graph.src edge.val ≠ v)
    have entryRead :=  drawnFirstPointer d₀ S ready capacity root side t wireFit peerFit wireWide peerWide
      bitsIn cut (fun _ => by rw [bitsRead,cutRead,idx])
    have location : lo = (if d₀.core root then chunk%grain else chunk) := sides.2
    refine entryRead.trans ?_
    rw [bitsRead,cutRead,location]
  · simp [BlockRef.cableNumber] at address


private theorem locatedCoordinates (root : d₀.edge) (side : Bool) (active : 0 < d₀.blocks.count root)
    (entry : Slot) (located : d₀.locate root side = some entry) :
    let h := if side then d₀.blocks.dst root else d₀.blocks.src root
    entry.host = (host h.1.2).val ∧ entry.group = h.1.1.val ∧ entry.block = h.2.val ∧
    entry.marked = decide (d₀.core root) := by
  intro h
  let edgeAt : Local d₀.blocks h := ⟨root,active,endpoint_incidence _ _ side⟩
  let role := (RR).address h edgeAt
  let expected : Slot := ⟨h.2.val,role.val,(host h.1.2).val,h.1.1.val,decide (d₀.core root)⟩
  have equal : expected = entry := Option.some.inj (by simpa only [locate,dite_eq_left active] using located)
  subst entry
  exact ⟨rfl,rfl,rfl,rfl⟩

private theorem emittedIncidentHome (root : d₀.edge) (t : Fin (d₀.blocks.count root))
    (v : W.graph.Site) (edge : Incident W.graph v) (wire : (d₀.emission.units ⟨root,t⟩).1 = edge.val) :
    (if decide (W.graph.src edge.val ≠ v) then d₀.blocks.dst root else d₀.blocks.src root) =
      DescentSharedCableNames.Stage.home A v := by
  by_cases source : W.graph.src edge.val=v
  · simp only [source,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false]
    have src := DescentResetWindowFields.src_at A native d₀.blocks d₀.core d₀.emission root t
    rw [wire,source] at src
    exact src.symm
  · rw [ite_eq_left (decide_eq_true source)]
    have dst := DescentResetWindowFields.dst_at A native d₀.blocks d₀.core d₀.emission root t
    rw [wire,edge.property.resolve_left source] at dst
    exact dst.symm

private theorem locatedIncident (root : d₀.edge) (t : Fin (d₀.blocks.count root))
    (v : W.graph.Site) (edge : Incident W.graph v) (wire : (d₀.emission.units ⟨root,t⟩).1 = edge.val)
    (entry : Slot) (located : d₀.locate root (decide (W.graph.src edge.val ≠ v)) = some entry) :
    entry.host = (host (A.pos v).2).val ∧ entry.group = (A.pos v).1.val ∧ entry.block = (A.block v).val := by
  have found := locatedCoordinates d₀ root _ (Nat.zero_lt_of_lt t.isLt) entry located
  have homeAt := emittedIncidentHome d₀ root t v edge wire
  exact ⟨found.1.trans (congrArg (fun axis => (host axis.1.2).val) homeAt),
    found.2.1.trans (congrArg (fun axis => axis.1.1.val) homeAt),
    found.2.2.1.trans (congrArg (fun axis => axis.2.val) homeAt)⟩


private theorem firstNumberedReceipt (capacity : A.cap=L) (root : d₀.edge) (side : Bool)
    (active : 0 < d₀.blocks.count root) {w : ℕ} (bitsIn cut : Cell (w+2)) (result : Pointer)
    (shown : let h:=if side then d₀.blocks.dst root else d₀.blocks.src root
      let edge : Local d₀.blocks h:=⟨root,active,endpoint_incidence _ _ side⟩
      let j:=(RR).address h edge
      let actual:=d₀.digits S ready capacity h.2 j (host h.1.2) h.1.1
      Pointer.ofKey 0 (resolve (Public.fragment (decide (d₀.core root)) actual.1 actual.2 bitsIn cut))=result) :
    ∃ atSlot : Slot, d₀.locate root side=some atSlot ∧
      let actual:=d₀.numbered S ready capacity atSlot.block atSlot.role atSlot.host atSlot.group
      Pointer.ofKey 0 (resolve (Public.fragment atSlot.marked actual.1 actual.2 bitsIn cut))=result := by
  let h:=if side then d₀.blocks.dst root else d₀.blocks.src root
  let edge : Local d₀.blocks h:=⟨root,active,endpoint_incidence _ _ side⟩
  let role:=(RR).address h edge
  refine ⟨⟨h.2.val,role.val,(host h.1.2).val,h.1.1.val,decide (d₀.core root)⟩,?_,?_⟩
  · simp only [locate,dite_eq_left active,h,edge,role]
  · simpa only [numbered_entry] using shown

private theorem markedAtSlot (root : d₀.edge) (side : Bool) (entry : Slot) (found : d₀.locate root side = some entry) :
    entry.marked=decide (d₀.core root) := by
  by_cases active : 0 < d₀.blocks.count root
  · exact (locatedCoordinates d₀ root side active entry found).2.2.2
  · simp only [locate,dite_eq_right active] at found
    cases found

private theorem roleAtSlot (root : d₀.edge) (side : Bool) (entry : Slot) (found : d₀.locate root side = some entry)
    (query : Fin H) (here : entry.host=query.val) (recipient : Fin prior)
    (receiver : DescentRawCablePanel.DepotRAM.Material.Route.receiver prior pitch query = some recipient)
    (positive : 0<pitch) (socket : Fin prior × Fin O) (path : Fin (breadth degree))
    (rawAddress : ∀ {h : Stage.Host (Fin groups) U k} (edge : Local d₀.blocks h),
      edge.val = root → d₀.observed.loc (d₀.observed.raw h edge) = socket)
    (visited : Gather.select (Gather.reaching R) recipient path = some socket.1) :
    entry.role = (finProdFinEquiv (path,socket.2)).val := by
  by_cases active : 0 < d₀.blocks.count root
  · let h:=if side then d₀.blocks.dst root else d₀.blocks.src root
    let edge : Local d₀.blocks h:=⟨root,active,endpoint_incidence _ _ side⟩
    let role:=(RR).address h edge
    let expected : Slot := ⟨h.2.val,role.val,(host h.1.2).val,h.1.1.val,decide (d₀.core root)⟩
    have equal : expected = entry := Option.some.inj (by simpa only [locate,dite_eq_left active] using found)
    subst entry
    have region : host h.1.2 = query := Fin.ext here
    have venue := d₀.receiver_on_tape h positive
    rw [region,receiver] at venue
    have picked : Gather.select (Gather.reaching R) (d₀.observed.venue h).1 path =
        some (d₀.observed.loc (d₀.observed.raw h edge)).1 := by
      rw [←Option.some.inj venue,rawAddress edge rfl]
      exact visited
    have roleEq := d₀.role_at_visit h edge path picked
    change ((RR).address h edge).val = _
    rw [roleEq,rawAddress edge rfl]
  · simp only [locate,dite_eq_right active] at found
    cases found


end
end Hierarchy.DescentDatedAddressBook.SignedDrawing

namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {k i z D wire hist w short a : ℕ}
variable {W : MarkedWorld F d P bits} {prior : Reached W G q ε S k i z D wire hist}
set_option quotPrecheck false
attribute [local irreducible] BitDescription.scannedRows DescentBundleHistory.WorldShape.follow DescentBundleHistory.WorldShape.selected DescentBundleHistory.WorldShape.transport OrdinaryModel.publicBooks Stage.nativeParts physicalRows DepotRAM.chip packDonor StarKeys.nativeKey OrdinaryLink.donorKey OrdinaryLink.measuredDonors
local notation "A" => prior.placement
local notation "J" => Fin (S.groupCount i)
local notation "V" => prior.V
local notation "native" => prior.order.trans Fin.valEmbedding
local notation "rank" => groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)
variable {he : 0≤ε} {choice : (prior.placement.stage.result he).Choice}
    {n : Normalize ((prior.placement.stage.result he).state choice)}
variable {z' D' : ℕ} {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink prior he prior.placement.stage choice n next) (port : MeterPort prior)
local notation "H" => port.hosts
local notation "T" => (A).stage
local notation "home" => scanHomeAt he T
local notation "color" => scanColorAt he T
local notation "addr" => nativeAddress he T
local notation "rr" => BitDescription.scannedRows he T
local notation "lay" => bestLayout (branchWidth G (fun _ : (rr).pairs=>(T).z) ((rr).profile choice))
local notation "bytes" => donorNameBits (T).k (T).Δ
local notation "slots" => 2^(packExponent 20 (T).Δ)+2
local notation "gain" => gainExponent 20 (T).Δ
local notation "grp" => Equiv.refl J
local notation "hosts" => port.vertex
local notation "peers" => rotor A rank
variable (win : Fin (S.groupCount i)×prior.V→Fin (2^k)→Cell a) (hm : 0<port.groupsPerWord)
variable (named : prior.placement.SiteNamed (groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)))
    (fit : ∀u,(win (prior.placement.pos u) (prior.placement.block u)).val<2^short)
    (winner : ∀u,(win (prior.placement.pos u) (prior.placement.block u)).val=
      1+2*heap (nativeAddress he prior.placement.stage (scanHomeAt he prior.placement.stage u)).2+
        (scanColorAt he prior.placement.stage u).toNat)
    (df : prior.placement.degree<2^short)
    (order : ∀e f,(prior.order e).val<(prior.order f).val ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
variable (profile : ℕ)
variable (b : ℕ) (m : Memory w)
    (sumSize : (shape (2^k) prior.placement.degree (2*prior.placement.cap) profile).outputBits*port.groupsPerWord≤w)
    (stored :
      let rankAt:=groupRank (Fin.valEmbedding : Fin (S.groupCount i) ↪ ℕ) (prior.vertex.trans Fin.valEmbedding)
      let shape₀:=shape (2^k) prior.placement.degree (2*prior.placement.cap) profile
      let world:=terrain (short:=short) prior.placement (prior.order.trans Fin.valEmbedding)
        S prior.valid (cableNames k rankAt) win (rotor prior.placement rankAt)
      let partsAt:=spread (Equiv.refl (Fin (S.groupCount i))).toEmbedding port.vertex world
      let inputs:=Gather.flat (Gather.descriptorInputs (K:=2^(k+1)) shape₀ prior.placement.cap partsAt)
      ∀j,m (b+j.val)=((DescentPacking.PackedMatch.topologyWords (M:=port.groupsPerWord) shape₀ inputs j).val:Computability.VPVNP.BurstRAM.Word w))
variable (dest : ℕ) (issued : Memory w)
    (roster : Fin port.hosts→Fin prior.placement.degree→Option (Fin port.hosts))
    (mounted : ∀(z : Fin (S.groupCount i)×prior.V) j,roster (port.vertex z.2) j=
      (rotor prior.placement (groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)) z j).map
        (fun h=>port.vertex h.2))
local notation "fmt" => Stage.shapeOf (short:=short) A bytes
local notation "measured" => Stage.nativeParts (short:=short) A native S prior.valid rank win grp hosts hm profile dest issued roster (A).hub lay bytes

open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator

local notation "sampleSlot" => DescentRawCablePanel.slot A S prior.valid native hosts grp (rr).pick
local notation "oldPorts" => S.groupCount i*(2^k)*(A).cap

variable (birth :
    let stage:=prior.placement.stage
    let actor:=scanHomeAt he stage
    let tint:=scanColorAt he stage
    let flow:=nativeTraffic W.graph W.core actor
    let limit:=prior.placement.cap
    let shape₀:=shape (2^k) prior.placement.degree (2*limit) profile
    let cellAt:=Stage.slot he prior.placement (Equiv.refl (Fin (S.groupCount i))).toEmbedding port.vertex hm
    ∀c : ScanColonies he stage,∀e : Matched flow limit (thinList actor tint c) (thickList actor tint c),
      ∃j : Fin shape₀.pairs,j.val=(pairNumber (DescentPacking.amount (live flow))
        (slabPacking flow limit (thinList actor tint c) (thickList actor tint c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=DescentPacking.PackedMatch.SixBirths.slot (cellAt c).2 j q
        DescentPacking.PackedMatch.SixBirths.atom stage.z (digit (shape₀.digit+1) ip.val (issued (dest+(cellAt c).1.val)).val) ip.val=
          some (stage.z,DescentTerminalEpochFlags.encode ((BitDescription.scannedRows he stage).profile choice ⟨c,e⟩),q.val))

local notation "N" => rawGraph he T choice
local notation "owner" => rawOwner he T choice n ((rr).state choice) (originalId _)
local notation "positiveRows" => DescentRawCablePanel.Live A (rr).pick
local notation:max "units" h:arg j:arg => liveMass (report (T).k gain slots
  (DepotRAM.seatDonor fmt profile G.b slots (measured h (groupSeat j).1) (groupSeat j).2.1 (groupSeat j).2.2.1)
  (groupSeat j).2.2.2)

open DescentSharedCableNames DescentHaloPackedRebase DescentParallelBase.ParentFilter
local notation "homeAt" => newSite W.graph (rr).pick lay (rr).pack
local notation:max "ctr" e:arg => mergeHub ticket.donorHub (T).k gain (ticket.donorKey (homeAt e))
local notation "P₀" => breadth (A).degree
local notation "Q" => 2^((T).k+1)*slots
local notation "K₀" => (P₀+1)*DepotRAM.Material.roles fmt
local notation "pitch" => (2^((T).k+1)-1)*slots
variable (fieldBits : ℕ)
local notation "form" => rawFormat (G:=G) (prior:=prior) profile pitch fieldBits
local notation "roomAt" => original_parent_room ticket port win hm named fit winner df order profile b m sumSize stored
                            dest issued roster mounted birth pitch fieldBits roster
local notation:max "rev" h:arg => digest (DepotRAM.Material.reverseEntries fmt roster h)

local notation:max "cell" h:arg j:arg => originalRecord ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch fieldBits h (groupSeat j).1 (groupSeat j).2
local notation:max "current" x:arg => n.destination (rawInput he T choice ((rr).state choice) x)
local notation:max "venue" x:arg => ticket.parentVenue port.enough (next.placement.pos (current x)).2
local notation:max "endRack" e:arg => hosts (ticket.donorKey (homeAt e)).1.2
local notation:max "endLow" e:arg => SiteDecode.localNumber (T).k slots (ctr e)

variable (age:i<S.length) (radix:S.radix=2^k)

variable (B:OrdinaryModel he prior.placement.stage choice (Fin (S.groupCount i)×prior.V))
local notation "world" => (B.named he T choice prior.order).result
local notation "act" => B.rawSite he T choice
variable (coh:n.result=(B.named he prior.placement.stage choice prior.order).result)
variable (places:∀x:(rawGraph he prior.placement.stage choice).Site,
  cast (congrArg (fun u:MarkedWorld F d P bits=>u.graph.Site) coh)
    (n.destination (rawInput he prior.placement.stage choice ((BitDescription.scannedRows he prior.placement.stage).state choice) x))=
    B.rawSite he prior.placement.stage choice x)
local notation "A₁" => modelStage (next:=next) B coh
local notation:max "raster₁" x:arg => ticket.parentVenue port.enough ((A₁).pos (act x)).2
local notation "key" => B.chart.key he T choice
local notation "last" => DescentSixParty.MarkedWorld.address (W.selected G (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice))
  key B.chart.hub (T).k gain
local notation:max "survives" e:arg => last (homeAt ((N).src (e).val))≠last (homeAt ((N).dst (e).val))
local notation:max "valueAt" e:arg => cell (sampleSlot e).1 (sampleSlot e).2
variable (pathWidth:breadth prior.placement.degree<2^fieldBits)
  (ticketWidth:(breadth prior.placement.degree+1)*DepotRAM.Material.roles
    (Stage.shapeOf (short:=short) prior.placement (donorNameBits prior.placement.stage.k prior.placement.stage.Δ))≤2^fieldBits)
open DescentParallelBase DescentOrdinaryParentSupport DescentSharedCableNames DescentSixParty.MarkedWorld
local notation "ok" => model_bounds (next:=next) B coh
local notation "eqG" => model_grain ticket B coh
variable (reciprocal:∀v u j,roster v j=some u→∃l,roster u l=some v)
open DescentDatedAddressBook DescentRawCablePanel.DepotRAM.Material.Route
variable {newH:ℕ} (hostRoom:Fintype.card next.V≤newH)
local notation "newHost" => next.vertex.trans (Fin.castLEEmb hostRoom)
variable (space :
    let stage := prior.placement.stage
    let sourceCount := 2^(stage.k+1)*(2^(packExponent 20 stage.Δ)+2)
    let localRoles := DepotRAM.Material.roles
      (Stage.shapeOf (short:=short) prior.placement (donorNameBits stage.k stage.Δ))
    Fused.capacity prior.placement.degree sourceCount
      ((breadth prior.placement.degree+1)*localRoles) next.placement.cap≤2^fieldBits)
local notation "diagram" => actualModelDrawing ticket port win hm named fit winner df order profile b m sumSize stored
  dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal hostRoom space

open DescentBundleHistory DescentPackedOperand DescentOperandStateBanks DescentParallelBase Computability.BorderVNP.Crossing
variable {p shapes : ℕ} (arch : Archive W) (hp : 0<p) (one : 1 ≤ shapes) (pin : ∀x,p∣bits x)
    (sh : WorldShape p shapes arch.bit) (unit : p∣prior.placement.stage.z)
    (use : OrdinaryModel.PublicUse he prior.placement.stage choice prior.order B arch hp one pin sh unit)
local notation "root" => OrdinaryModel.PublicUse.parent he T choice prior.order B arch hp one pin sh unit use
local notation "arg" => OrdinaryModel.PublicUse.finalOperand he T choice prior.order B arch hp one pin sh unit use
local notation "name₁" => cableNames k (groupRank Fin.valEmbedding ((newHost).trans Fin.valEmbedding))
local notation "live₁" => Public.endpoint A₁ (originalId (world).graph.Edge) S ok name₁
local notation "cap₁" => (model_shape (next:=next) B coh).1
local notation "physicalCore" => fun e => e ∈ (DescentSixParty.MarkedWorld.coalesced (W.selected G (rr).pick
  (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice)) key B.chart.hub (T).k gain).core
local notation "publicEmits" => OrdinaryModel.PublicUse.emitted he T choice prior.order B arch hp one pin sh unit A₁ S ok eqG use
private theorem sameCoreIndex {u v : ℕ} {p₁ p₂ : Prop} {d₁ : Decidable p₁} {d₂ : Decidable p₂}
    (same : p₁ ↔ p₂) : @ite ℕ p₁ d₁ u v = @ite ℕ p₂ d₂ u v := by
  by_cases h : p₁
  · rw [ite_eq_left h,ite_eq_left (same.mp h)]
  · rw [ite_eq_right h,ite_eq_right (fun k => h (same.mpr k))]

local instance chronologicalPublicEdgeFintype : Fintype (diagram).edge := (diagram).finiteEdge
local instance chronologicalPublicRawFintype : Fintype (diagram).raw := (diagram).finiteRaw
local instance chronologicalPublicTicketFintype : Fintype (diagram).ticket := (diagram).finiteTicket
local notation "nativeRow" => (diagram).digits S ok cap₁
local notation "rr₁" => Measured.roster (diagram).blocks roster reciprocal (diagram).observed
set_option maxHeartbeats 1800000

/-- The original signed parent and the actually occupied argument of the
normalized graph have the same first serial, peer and remaining bit block. -/
theorem model_public_operand {wordBits : ℕ} (bitsIn cut : Cell (wordBits+2)) (bitsRead : bitsIn.val=use.chunk)
    (cutRead : cut.val=(T).z/p) (wireFit : (A₁).cap≤2^fieldBits) (peerFit : (A₁).degree≤2^fieldBits)
    (wireWide : (A₁).cap≤2^(wordBits+2)) (peerWide : (A₁).degree≤2^(wordBits+2)) :
    DescentDatedAddressBook.SignedDrawing.blockPointerResult diagram S ok cap₁ root use.node.1
      (fun w => arg = .inl w) use.chunk ((T).z/p) bitsIn cut := by
  refine DescentDatedAddressBook.SignedDrawing.observedBlockPointer
    (F:=F) (Pin:=P) (U:=next.V) (W:=world) (G:=G) («A»:=A₁) («native»:=originalId (world).graph.Edge)
    (R:=roster) (symm:=reciprocal) («host»:=newHost) («pitch»:=pitch) («space»:=space)
    (p:=p) (wordBits:=wordBits) diagram S ok cap₁ root use.node.1
    (fun w => arg = .inl w) use.chunk ((T).z/p) ?_ wireFit peerFit wireWide peerWide bitsIn cut bitsRead cutRead
  have emittedProof := publicEmits
  rcases emittedProof with ⟨w,t,rawSeen,offset,cableAt,laneAt⟩
  refine ⟨w,t,rawSeen,offset,?_,?_⟩
  · refine cableAt.trans ?_
    apply congrArg (fun index : ℕ => some (((diagram).emission.units ⟨root,t⟩).1,index))
    exact sameCoreIndex (p₁:=(physicalCore) root) (p₂:=(diagram).core root) Iff.rfl
  · exact laneAt.trans (sameCoreIndex (p₁:=(physicalCore) root) (p₂:=(diagram).core root) Iff.rfl)

/-- The four native numerals at the occupied slot are exactly its reached pointer. -/
theorem model_firstCable {wordBits : ℕ} (bitsIn cut : Cell (wordBits+2)) (bitsRead : bitsIn.val=use.chunk)
    (cutRead : cut.val=(T).z/p) (wireFit : (A₁).cap≤2^fieldBits) (peerFit : (A₁).degree≤2^fieldBits)
    (wireWide : (A₁).cap≤2^(wordBits+2)) (peerWide : (A₁).degree≤2^(wordBits+2)) :
    ∃edge : Incident (world).graph use.node.1,∃low : ℕ,∃fits : (low+1)*p≤(world).graph.width edge.val,
    arg=.inl ⟨.inl edge,low,fits⟩ ∧
    ∃child : Fin ((diagram).blocks.count root),
    let unit₁:=(diagram).emission.units ⟨root,child⟩
    let side:=decide ((world).graph.src edge.val≠use.node.1)
    let h:=if side then (diagram).blocks.dst root else (diagram).blocks.src root
    let edgeAt : DescentParallelBase.Local (diagram).blocks h:=
      ⟨root,Nat.zero_lt_of_lt child.isLt,DescentDatedAddressBook.SignedDrawing.endpoint_incidence _ _ side⟩
    let slot:=(rr₁).address h edgeAt
    unit₁.1=edge.val ∧ child.val=use.chunk/((T).z/p) ∧
    Pointer.ofKey 0 (resolve (Public.fragment (decide ((diagram).core root))
      (nativeRow h.2 slot (newHost h.1.2) h.1.1).1
      (nativeRow h.2 slot (newHost h.1.2) h.1.1).2 bitsIn cut))=
      next.firstCable hp (Reached.originalSite coh use.node.1) (Reached.originalIncident coh use.node.1 edge) low
        (Reached.original_fit coh use.node.1 edge low fits) := by
  have localReceipt1 := model_public_operand ticket port win hm named fit
    winner df order profile b m sumSize stored dest issued roster mounted birth fieldBits age radix B coh places
    pathWidth ticketWidth reciprocal hostRoom space arch hp one pin sh unit use bitsIn cut bitsRead cutRead
    wireFit peerFit wireWide peerWide
  rcases localReceipt1 with ⟨edge,lo,fit,occ,child,emitted,idx,num⟩
  refine ⟨edge,lo,fit,occ,child,emitted,idx,?_⟩
  refine num.trans (next.firstCable_on_tape coh hp ?_ ok use.node.1 edge lo fit
    ((diagram).emission.units ⟨root,child⟩) emitted).symm
  exact Function.Embedding.ext fun e=>next.edgeName (Nat.succ_pos i) e

local notation "node" => OrdinaryModel.PublicNode he T choice prior.order B arch
local notation "slotIndex" => OrdinaryModel.PublicArg he T choice prior.order B arch hp one pin sh unit
local notation "observed" => OrdinaryModel.publicOperand he T choice prior.order B arch hp one pin sh unit
local notation "Use" => OrdinaryModel.PublicUse he T choice prior.order B arch hp one pin sh unit
local notation:max "parentOf" u:arg => OrdinaryModel.PublicUse.parent he T choice prior.order B arch hp one pin sh unit u

/-- Every actual named cable operand has an original donor, and the fragment
at its own recorded visit decodes to precisely that requested reached pointer. -/
theorem occupied_firstCable (x : node) (j : slotIndex x) (edge : Incident (world).graph x.1) (lo : ℕ)
    (bitFit : (lo+1)*p≤(world).graph.width edge.val) (hit : observed x j=.inl ⟨.inl edge,lo,bitFit⟩)
    {wordBits : ℕ} (wireFit : (A₁).cap≤2^fieldBits) (peerFit : (A₁).degree≤2^fieldBits)
    (wireWide : (A₁).cap≤2^(wordBits+2)) (peerWide : (A₁).degree≤2^(wordBits+2)) :
    ∃u : Use,u.node=x ∧ HEq u.arg j ∧
    ∀(bitsIn cut : Cell (wordBits+2)),bitsIn.val=u.chunk→cut.val=(T).z/p→
    ∃child : Fin ((diagram).blocks.count (parentOf u)),
    let unit₁:=(diagram).emission.units ⟨parentOf u,child⟩
    let side:=decide ((world).graph.src edge.val≠x.1)
    let h:=if side then (diagram).blocks.dst (parentOf u) else (diagram).blocks.src (parentOf u)
    let edgeAt : DescentParallelBase.Local (diagram).blocks h:=
      ⟨parentOf u,Nat.zero_lt_of_lt child.isLt,DescentDatedAddressBook.SignedDrawing.endpoint_incidence _ _ side⟩
    let slot:=(rr₁).address h edgeAt
    unit₁.1=edge.val ∧ child.val=u.chunk/((T).z/p) ∧
    Pointer.ofKey 0 (resolve (Public.fragment (decide ((diagram).core (parentOf u)))
      (nativeRow h.2 slot (newHost h.1.2) h.1.1).1
      (nativeRow h.2 slot (newHost h.1.2) h.1.1).2 bitsIn cut))=
    next.firstCable hp (Reached.originalSite coh x.1) (Reached.originalIncident coh x.1 edge) lo
      (Reached.original_fit coh x.1 edge lo bitFit) :=by
  have localReceipt2 := B.public_origin he T choice prior.order arch hp one pin sh unit x j edge lo bitFit hit
  rcases localReceipt2 with ⟨u,rfl,hh⟩
  have eqn:=eq_of_heq hh
  subst j
  refine ⟨u,rfl,HEq.rfl,?_⟩
  intro bitsIn cut bitsRead cutRead
  have localReceipt3 := model_firstCable ticket port win hm named fit winner df order profile
    b m sumSize stored dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal
    hostRoom space arch hp one pin sh unit u bitsIn cut bitsRead cutRead wireFit peerFit wireWide peerWide
  rcases localReceipt3 with ⟨e,l,bound,actual,child,sent,idx,out⟩
  have same : (⟨.inl e,l,bound⟩:BlockRef p (boundaryWidth (world).graph u.node.1))=⟨.inl edge,lo,bitFit⟩:=
    Sum.inl.inj (actual.symm.trans hit)
  cases same
  exact ⟨child,sent,idx,out⟩

open DescentDatedAddressBook.SignedDrawing
local notation "snap" => (diagram).numbered S ok cap₁
local notation:max "locate" u:arg => (diagram).locate (parentOf u)

theorem numbered_firstCable (x : node) (j : slotIndex x) (edge : Incident (world).graph x.1) (lo : ℕ)
    (bitFit : (lo+1)*p≤(world).graph.width edge.val) (hit : observed x j=.inl ⟨.inl edge,lo,bitFit⟩)
    {wordBits : ℕ} (wireFit : next.placement.cap≤2^fieldBits) (peerFit : next.placement.degree≤2^fieldBits)
    (wireWide : next.placement.cap≤2^(wordBits+2)) (peerWide : next.placement.degree≤2^(wordBits+2)) :
    ∃u : Use,u.node=x ∧ HEq u.arg j ∧
      ∀(bitsIn cut : Cell (wordBits+2)),bitsIn.val=u.chunk→cut.val=(T).z/p→∃atSlot : SignedDrawing.Slot,
        locate u (decide ((world).graph.src edge.val≠x.1))=some atSlot ∧
        let actual:=snap atSlot.block atSlot.role atSlot.host atSlot.group
        Pointer.ofKey 0 (resolve (Public.fragment atSlot.marked actual.1 actual.2 bitsIn cut))=
          next.firstCable hp (Reached.originalSite coh x.1) (Reached.originalIncident coh x.1 edge) lo
            (Reached.original_fit coh x.1 edge lo bitFit) :=by
  have shape:=model_shape (next:=next) B coh
  have localReceipt4 := occupied_firstCable ticket port win hm named fit winner df order profile b m sumSize
    stored dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal hostRoom
    space arch hp one pin sh unit x j edge lo bitFit hit (shape.1.symm ▸ wireFit) (shape.2.1.symm ▸ peerFit)
    (shape.1.symm ▸ wireWide) (shape.2.1.symm ▸ peerWide)
  rcases localReceipt4 with ⟨u,who,which,reads⟩
  refine ⟨u,who,which,?_⟩
  intro bitsIn cut origBit origCut
  have localReceipt5 := reads bitsIn cut origBit origCut
  rcases localReceipt5 with ⟨child,_,_,receipt⟩
  exact DescentDatedAddressBook.SignedDrawing.firstNumberedReceipt diagram S ok cap₁ (parentOf u)
    (decide ((world).graph.src edge.val ≠ x.1)) (Nat.zero_lt_of_lt child.isLt) bitsIn cut _ receipt

local notation "raw" => DescentRawCablePanel.Live A (rr).pick
local notation "socket" => DescentRawCablePanel.shortSlot A S prior.valid native hosts (rr).pick
local notation "getReceiver" => DescentRawCablePanel.DepotRAM.Material.Route.receiver H

/-- The selected packed role is the path supplying the actual earlier donor
times the true seat capacity plus that raw row's own old block, cable and role. -/
theorem actual_donated_role (side : Bool) (donated : raw) (same : donated.val=use.cable.val)
    (entry : SignedDrawing.Slot) (atSlot : locate use side=some entry)
    (query : Fin newH) (here : entry.host=query.val) (recipient : Fin H)
    (atReceiver : getReceiver ((2^((T).k+1)-1)*slots) query=some recipient)
    (path : Fin P₀) (read : Gather.select (Gather.reaching roster) recipient path=some (socket donated).1) :
    entry.role=(finProdFinEquiv (path,(socket donated).2)).val :=by
  have pitchPositive : 0 < (2^((T).k+1)-1)*slots :=
    Nat.mul_pos (Nat.sub_pos_of_lt (Nat.one_lt_two_pow (Nat.zero_lt_succ _).ne')) (Nat.succ_pos _)
  refine DescentDatedAddressBook.SignedDrawing.roleAtSlot diagram (parentOf use) side entry atSlot
    query here recipient atReceiver pitchPositive (socket donated) path ?_ read
  intro h edgeAt sameParent
  rcases edgeAt with ⟨id,isLive,endpoint⟩
  change id = parentOf use at sameParent
  subst id
  rcases donated with ⟨wire,positive⟩
  change wire=use.cable.val at same
  subst wire
  rfl

theorem actual_donated_receiver (edge : Incident (world).graph use.node.1) (lo : ℕ)
    (within : (lo+1)*p≤(world).graph.width edge.val) (hit : arg=.inl ⟨.inl edge,lo,within⟩)
    (entry : SignedDrawing.Slot) (located : locate use (decide ((world).graph.src edge.val≠use.node.1))=some entry) :
    let v:=Reached.originalSite coh use.node.1
    entry.host=(next.vertex (next.placement.pos v).2).val ∧
    entry.group=(next.placement.pos v).1.val ∧ entry.block=(next.placement.block v).val :=by
  intro v
  have localReceipt6 := publicEmits
  rcases localReceipt6 with ⟨w,t,occ,idx,address,_⟩
  have same : w=⟨.inl edge,lo,within⟩:=Sum.inl.inj (occ.symm.trans hit)
  have readCable := (congrArg
    (fun w : BlockRef p (boundaryWidth (world).graph use.node.1) => w.cableNumber (world).graph use.node.1)
    same.symm).trans address
  have emits : ((diagram).emission.units ⟨parentOf use,t⟩).1=edge.val:=(congrArg Prod.fst (Option.some.inj readCable)).symm
  have coords := DescentDatedAddressBook.SignedDrawing.locatedIncident diagram (parentOf use) t use.node.1 edge emits entry located
  have localReceipt7 := next.original_cell coh use.node.1
  rcases localReceipt7 with ⟨posAt,blockAt⟩
  change entry.host=(next.vertex ((A₁).pos use.node.1).2).val ∧ entry.group=((A₁).pos use.node.1).1.val ∧ entry.block=((A₁).block use.node.1).val at coords
  refine ⟨coords.1.trans ?_,coords.2.1.trans ?_,coords.2.2.trans ?_⟩
  · exact congrArg (fun a : Fin (S.groupCount (i+1)) × next.V => (next.vertex a.2).val) posAt
  · exact congrArg (fun a : Fin (S.groupCount (i+1)) × next.V => a.1.val) posAt
  · exact congrArg Fin.val blockAt

theorem actual_donated_mark (side : Bool) (entry : SignedDrawing.Slot) (found : locate use side=some entry) :
    entry.marked=DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role use.cable.val)
      (decide (anchor (rr).pick use.cable.val∈W.core)) :=by
  have mark := DescentDatedAddressBook.SignedDrawing.markedAtSlot diagram (parentOf use) side entry found
  have nativeMark := DescentOrdinarySignedMeta.core_role W G (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack
    ((rr).profile choice) (B.chart.key he T choice) B.chart.hub (T).k (gainExponent 20 (T).Δ) (parentOf use)
  exact mark.trans ((decide_eq_decide.mpr Iff.rfl).trans nativeMark.symm)


end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

-- Limit premise-search indexing of these expanded chronological signatures during export.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun current =>
    ["model_public_operand", "model_firstCable", "occupied_firstCable", "numbered_firstCable", "actual_donated_role", "actual_donated_receiver", "actual_donated_mark"] ++ current

end OAI
