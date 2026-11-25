import OAI.Hierarchy.DescentPrivateDepotPhase
import OAI.Hierarchy.DescentDatedOriginalDonorRead
import OAI.Hierarchy.DescentOrdinaryRawObserved

namespace OAI
/-! # True capture flags and the signed anchor in each original material seat -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
/-- Seat and group are the two projections of the original flattened census
address. The external rank word only affects field four. -/
def groupSeat {G r cap : ℕ} (j : Fin ((G*r*cap)*11)) : Fin G × (Fin r × Fin cap × Fin 11) :=
  let (seat,role):=finProdFinEquiv.symm j
  let (gx,t):=finProdFinEquiv.symm seat
  let (g,x):=finProdFinEquiv.symm gx
  (g,x,t,role)

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {k i z D wire hist w short a : ℕ}
variable {W : MarkedWorld F d P bits} {prior : Reached W G q ε S k i z D wire hist}
set_option quotPrecheck false
attribute [local irreducible] Stage.nativeParts physicalRows DepotRAM.chip packDonor StarKeys.nativeKey OrdinaryLink.donorKey OrdinaryLink.measuredDonors
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
local notation "r" => 2^k
local notation "rr" => BitDescription.scannedRows he T
local notation "lay" => bestLayout (branchWidth G (fun _ : (rr).pairs=>(T).z) ((rr).profile choice))
local notation "bytes" => donorNameBits (T).k (T).Δ
local notation "slots" => 2^(packExponent 20 (T).Δ)+2
local notation "gain" => gainExponent 20 (T).Δ
local notation "grp" => Equiv.refl J
local notation "hosts" => port.vertex
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
local notation "oldPorts" => S.groupCount i*r*(A).cap

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

include named fit winner df order sumSize stored mounted birth in
/-- Reading the actual chip in the earlier matched register board decodes the
same donor that was installed in the chronological private meter. -/
theorem raw_seat_donor (h : Fin H) (g : J) (x : Fin r) (t : Fin (A).cap) :
  DepotRAM.seatDonor fmt profile G.b slots (measured h g) x t =
    ticket.measuredDonors hosts h (finProdFinEquiv (finProdFinEquiv (g,x),t)) :=by
  have chart : ticket.donorChart.col=addr:=eq_of_heq ticket.donorChart.native
  have key : ticket.donorKey=StarKeys.nativeKey W.graph W.core home color (T).cap addr ticket.donorChart.same lay :=by
    unfold OrdinaryLink.donorKey IssuedDonorChart.key
    exact congrArg (fun loc => StarKeys.nativeKey W.graph W.core home color (T).cap loc ticket.donorChart.same lay) chart
  have data:=Stage.all_seats A native S prior.valid rank win he grp hosts hm prior.valid.coordinates
    named fit winner df order profile b m sumSize stored choice dest issued roster mounted (A).hub
    ticket.donorChart.same lay birth slots bytes (T).k h g x t
  have seen := ticket.measuredDonors_publicHub port.vertex
  have aligned := seen.trans (congrArg (fun key₀ => physicalRows (a:=bytes) (hCode:=(T).k) A S prior.valid
    native hosts grp (rr).pick lay (rr).pack key₀ (fun v => (A).hub v.2) slots ((rr).profile choice)
    (relative (rr).pick lay (rr).pack key₀)) (congrArg (fun (f : _ ↪ _) => f.toFun) key))
  exact (congrArg unpackDonor data).trans ((DescentRawCablePanel.unpack_pack _).trans
    (congrFun (congrFun aligned.symm h) (finProdFinEquiv (finProdFinEquiv (g,x),t))))

def rawFormat (profile pitch bits : ℕ) : DepotRAM.Material.Setup :=
  ⟨profile,G.b,(T).k,gain,slots,pitch,bits⟩

variable (pitch bitsOut : ℕ)
    (rev : Cell (DepotRAM.chartBits (Stage.shapeOf (short:=short) prior.placement
      (donorNameBits prior.placement.stage.k prior.placement.stage.Δ))))
local notation "u" => rawFormat (G:=G) (prior:=prior) profile pitch bitsOut

local notation:max "parts" h:arg j:arg => (measured h (groupSeat j).1)
local notation:max "read_" h:arg j:arg i:arg => DepotRAM.Material.rawObserved fmt u (parts h j) rev (groupSeat j).2 i
local notation:max "sample" h:arg j:arg => ticket.issuedPanel hosts h j

include named fit winner df order sumSize stored mounted birth in
theorem raw_observation (h : Fin H) (j : Fin (oldPorts*11)) :
    read_ h j 2=((DepotRAM.Operand.datum true (sample h j)).toNat:Cell bitsOut) ∧
    read_ h j 3=((DepotRAM.Operand.datum false (sample h j)).toNat:Cell bitsOut) :=by
  let codes:=finProdFinEquiv.symm j
  let seatCode:=finProdFinEquiv.symm codes.1
  let gx:=finProdFinEquiv.symm seatCode.1
  have local_:=raw_seat_donor ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth h gx.1 gx.2 seatCode.2
  have lens : finProdFinEquiv (finProdFinEquiv (gx.1,gx.2),seatCode.2)=codes.1 :=
    (congrArg (fun z => finProdFinEquiv (z,seatCode.2))
      (finProdFinEquiv.apply_symm_apply seatCode.1)).trans (finProdFinEquiv.apply_symm_apply codes.1)
  have donor := local_.trans (congrArg (ticket.measuredDonors hosts h) lens)
  have observed := (congrArg (fun d₀ => report (T).k gain slots d₀ codes.2) donor).trans
    (ticket.donor_words hosts h j)
  have atSeat:=DepotRAM.Material.raw_flags fmt u (parts h j) rev (groupSeat j).2
  exact ⟨atSeat.1.trans (congrArg (fun v => ((DepotRAM.Operand.datum true v).toNat:Cell bitsOut)) observed),
    atSeat.2.trans (congrArg (fun v => ((DepotRAM.Operand.datum false v).toNat:Cell bitsOut)) observed)⟩

local notation "rawGraph_" => rawGraph he T choice
local notation "from_" => (originalId (((T).result he).state choice).graph.Site) ∘ rawInput he T choice ((rr).state choice)
local notation "owner_" => rawOwner he T choice n ((rr).state choice) (originalId _)

include ticket named fit winner df order sumSize stored mounted birth in
theorem raw_capture_fields (e : DescentRawCablePanel.Live A (rr).pick) :
    let position:=sampleSlot e
    let a:=decide (from_ ((rawGraph_).src e.val)=from_ ((rawGraph_).dst e.val))
    let b:=decide (owner_ ((rawGraph_).src e.val)=owner_ ((rawGraph_).dst e.val))
    read_ position.1 position.2 2=(a.toNat:Cell bitsOut) ∧ read_ position.1 position.2 3=((!a && b).toNat:Cell bitsOut) :=by
  dsimp only
  have recorded:=raw_observation ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch bitsOut rev (sampleSlot e).1 (sampleSlot e).2
  have captured:=ticket.capture_at hosts e
  exact ⟨recorded.1.trans (congrArg (fun b:Bool=>(b.toNat:Cell bitsOut)) captured.1),
    recorded.2.trans (congrArg (fun b:Bool=>(b.toNat:Cell bitsOut)) captured.2)⟩

include ticket named fit winner df order sumSize stored mounted birth in
theorem raw_capture_absent (h : Fin H) (j : Fin (oldPorts*11)) (absent : ¬∃e,sampleSlot e=(h,j)) :
    read_ h j 2=0 ∧ read_ h j 3=0 :=by
  have recorded:=raw_observation ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch bitsOut rev h j
  have none:=ticket.donor_captures_hole hosts h j absent
  dsimp only at none
  rw [ticket.donor_words hosts h j] at none
  exact ⟨recorded.1.trans (congrArg (fun v : Bool => (v.toNat:Cell bitsOut)) none.1),
    recorded.2.trans (congrArg (fun v : Bool => (v.toNat:Cell bitsOut)) none.2)⟩

local notation "widths" => normBits (A).cap G.b G.C G.k
local notation "inputBits" => bundleBits 3 bytes widths
local notation "batch" => port.groupsPerWord*(2^k*(A).cap)
local notation "saved" => (DescentPackedDonorSpace.banks port.base port.hosts oldPorts batch inputBits).source

include named fit winner df order sumSize stored mounted birth in
/-- The two physically issued material words and the earlier metered donor
memory agree on each live raw cable, even after either quotient has renamed its ends. -/
theorem raw_prior_flags (snapshot : Memory w) (pins : MeterPort.Pins ticket port snapshot)
    (lanes : 0 < batch) (bitsFit : inputBits*batch ≤ w) (e : DescentRawCablePanel.Live A (rr).pick) :
    let pos:=sampleSlot e
    let j:=finProdFinEquiv.symm pos.2
    let savedDonor:=DescentTerminalSignedGrainWord.chip (a:=inputBits) saved snapshot pos.1 j.1 lanes
    let observed:=report (T).k gain slots (unpackDonor (loc:=3) (a:=bytes) (c:=widths) savedDonor) j.2
    read_ pos.1 pos.2 2=((DepotRAM.Operand.datum true observed).toNat:Cell bitsOut) ∧
      read_ pos.1 pos.2 3=((DepotRAM.Operand.datum false observed).toNat:Cell bitsOut) :=by
  dsimp only
  have raw:=raw_capture_fields ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch bitsOut rev e
  have original:=MeterPort.capture_read ticket port snapshot pins lanes bitsFit e
  exact ⟨raw.1.trans (congrArg (fun b:Bool=>(b.toNat:Cell bitsOut)) original.1.symm),
    raw.2.trans (congrArg (fun b:Bool=>(b.toNat:Cell bitsOut)) original.2.symm)⟩

set_option maxHeartbeats 650000 in
theorem raw_anchor_field (sg : J×V) (x : Fin r) (t : Fin (A).cap) (role : Fin 11) :
    DepotRAM.Material.rawObserved fmt u (measured (hosts sg.2) sg.1) rev (x,t,role) 5 =
    (((DescentSharedCableNames.Stage.signedPanel A native S prior.valid (cableNames k rank) (sg,x)
      (t.castLE (by omega))).elim false (·.markedOut)).toNat:Cell bitsOut) :=by
  rw [DepotRAM.Material.raw_mark]
  let signedAt := Stage.physicalSigned A native S prior.valid rank grp hosts (hosts sg.2) sg.1
  let col := t.castLE (by omega : (A).cap≤2*(A).cap)
  let namesAt : Fin (r*(2*(A).cap)) → Cell (DescentSignedCableCodec.width (A).degree (A).cap) :=
    fun j => signedAt (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  have unpack := congrFun ((encode (DescentSignedCableCodec.width (A).degree (A).cap) (r*(2*(A).cap))).symm_apply_apply namesAt)
      (finProdFinEquiv (x,col))
  have atPair := congrArg (fun ix : Fin r × Fin (2*(A).cap) => signedAt ix.1 ix.2)
    (finProdFinEquiv.symm_apply_apply (x,col))
  have hit := Stage.physical_signed_read A native S prior.valid rank grp hosts sg x col
  have stored := atPair.trans hit
  have decoded := (congrArg (DescentSignedCableCodec.decode (A).degree (A).cap) (unpack.trans stored)).trans
    (DescentSignedCableCodec.decode_encode _)
  unfold DepotRAM.Material.rawAnchorMark Stage.nativeParts DepotRAM.operands
  exact congrArg (fun data : Option (DescentSharedCableNames.Stage.Live (A).degree (A).cap) =>
    ((data.elim false (·.markedOut)).toNat:Cell bitsOut)) decoded

/-- The original outgoing grain is the first grain of this exact old edge.
Thus the physical mark on every raw role anchored here is the old core bit. -/
theorem raw_anchor_core (e : DescentSharedCableNames.Stage.Positive A) (role : Fin 11) :
    let src:=W.graph.src e.val
    let z:=(A).pos src
    let t:=DescentSharedCableNames.Stage.outgoing A native S prior.valid e
    DepotRAM.Material.rawObserved fmt u (measured (hosts z.2) z.1) rev ((A).block src,t,role) 5=
      ((decide (e.val∈W.core)).toNat:Cell bitsOut) :=by
  dsimp only
  rw [raw_anchor_field]
  change (((DescentSharedCableNames.Stage.signedPanel A native S prior.valid (cableNames k rank)
    (DescentSharedCableNames.Stage.home A (W.graph.src e.val)) (Stage.headSlot A native S prior.valid e)).elim
    false (·.markedOut)).toNat:Cell bitsOut)=_
  have cable := Stage.origin_stored A native S prior.valid rank e
  dsimp only at cable
  have line : DescentSharedCableNames.Stage.signedPanel A native S prior.valid (cableNames k rank)
      (DescentSharedCableNames.Stage.home A (W.graph.src e.val)) (Stage.headSlot A native S prior.valid e) =
      some (Stage.sourceHandle A native S prior.valid rank e) :=
    (congrArg (DescentSharedCableNames.Stage.signedPanel A native S prior.valid (cableNames k rank)
      (DescentSharedCableNames.Stage.home A (W.graph.src e.val))) (Stage.origin_position A native S prior.valid e).symm).trans cable
  rw [line]
  simp [Stage.sourceHandle,DescentSharedCableNames.Stage.live,DescentSharedCableNames.Stage.isMarkedOut,Stage.originPort]


end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
