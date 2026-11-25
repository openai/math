import OAI.Hierarchy.DescentDatedTicketResidentFlags
import OAI.Hierarchy.DescentDatedTicketSockets
import OAI.Hierarchy.DescentOrdinaryResidentMark

namespace OAI
/-! # Every chosen socket at an authentic ordinary occurrence has the posted eight-word ticket -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {k i z D wire hist w short a : ℕ}
variable {W : MarkedWorld F d P bits} {prior : Reached W G q ε S k i z D wire hist}
set_option quotPrecheck false
set_option maxHeartbeats 1200000
local notation "A" => prior.placement
local notation "J" => Fin (S.groupCount i)
local notation "native" => prior.order.trans Fin.valEmbedding
local notation "rank" => groupRank (Fin.valEmbedding : Fin (S.groupCount i) ↪ ℕ) (prior.vertex.trans Fin.valEmbedding)
variable {he : 0≤ε} {choice : (prior.placement.stage.result he).Choice}
    {n : Normalize ((prior.placement.stage.result he).state choice)}
variable {z' D' : ℕ} {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink prior he prior.placement.stage choice n next) (port : MeterPort prior)
local notation "T" => (A).stage
local notation "home" => scanHomeAt he T
local notation "color" => scanColorAt he T
local notation "addr" => nativeAddress he T
local notation "r" => 2^k
local notation "rr" => BitDescription.scannedRows he T
local notation "lay" => bestLayout (branchWidth G (fun _ : (rr).pairs=>(T).z) ((rr).profile choice))
local notation "bytes" => donorNameBits (T).k (T).Δ
local notation "grp" => Equiv.refl J
local notation "hosts" => port.vertex
variable (win : Fin (S.groupCount i)×prior.V→Fin (2^k)→Cell a) (hm : 0<port.groupsPerWord)
variable (named : prior.placement.SiteNamed (groupRank (Fin.valEmbedding : Fin (S.groupCount i) ↪ ℕ) (prior.vertex.trans Fin.valEmbedding)))
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
      let format:=shape (2^k) prior.placement.degree (2*prior.placement.cap) profile
      let world:=terrain (short:=short) prior.placement (prior.order.trans Fin.valEmbedding)
        S prior.valid (cableNames k rankAt) win (rotor prior.placement rankAt)
      let partsAt:=spread (Equiv.refl (Fin (S.groupCount i))).toEmbedding port.vertex world
      let inputs:=Gather.flat (Gather.descriptorInputs (K:=2^(k+1)) format prior.placement.cap partsAt)
      ∀j : Fin (2^(k+1)*port.hosts * chunks (S.groupCount i) port.groupsPerWord),m (b+j.val)=((DescentPacking.PackedMatch.topologyWords (M:=port.groupsPerWord) format inputs j).val:Computability.VPVNP.BurstRAM.Word w))
variable (dest : ℕ) (issued : Memory w)
    (roster : Fin port.hosts→Fin prior.placement.degree→Option (Fin port.hosts))
    (mounted : ∀(z : Fin (S.groupCount i)×prior.V) j,roster (port.vertex z.2) j=
      (rotor prior.placement (groupRank (Fin.valEmbedding : Fin (S.groupCount i) ↪ ℕ) (prior.vertex.trans Fin.valEmbedding)) z j).map
        (fun h=>port.vertex h.2))
local notation "fmt" => Stage.shapeOf (short:=short) A bytes
local notation "measured" => Stage.nativeParts (short:=short) A native S prior.valid rank win grp hosts hm profile dest issued roster (A).hub lay bytes

open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator

variable (birth :
    let stage:=prior.placement.stage
    let actor:=scanHomeAt he stage
    let tint:=scanColorAt he stage
    let flow:=nativeTraffic W.graph W.core actor
    let limit:=prior.placement.cap
    let format:=shape (2^k) prior.placement.degree (2*limit) profile
    let cellAt:=DescentPacking.PackedMatch.Local.Stage.slot he prior.placement (Equiv.refl (Fin (S.groupCount i))).toEmbedding port.vertex hm
    ∀c : ScanColonies he stage,∀e : Matched flow limit (thinList actor tint c) (thickList actor tint c),
      ∃j : Fin format.pairs,j.val=(pairNumber (DescentPacking.amount (live flow))
        (slabPacking flow limit (thinList actor tint c) (thickList actor tint c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=DescentPacking.PackedMatch.SixBirths.slot (cellAt c).2 j q
        DescentPacking.PackedMatch.SixBirths.atom stage.z (digit (format.digit+1) ip.val (issued (dest+(cellAt c).1.val)).val) ip.val=
          some (stage.z,DescentTerminalEpochFlags.encode ((BitDescription.scannedRows he stage).profile choice ⟨c,e⟩),q.val))

variable (pitch bitsOut : ℕ)
    (rev : Cell (DepotRAM.chartBits (Stage.shapeOf (short:=short) prior.placement
      (donorNameBits prior.placement.stage.k prior.placement.stage.Δ))))
local notation "rawLayout" => rawFormat (G:=G) (prior:=prior) profile pitch bitsOut

local notation "rawGraph_" => rawGraph he T choice
local notation "from_" => (originalId (((T).result he).state choice).graph.Site) ∘ rawInput he T choice ((rr).state choice)
local notation "owner_" => rawOwner he T choice n ((rr).state choice) (originalId _)

open DescentDatedOperandCoordinates
local notation "parent_" e => (⟨DescentCableDonorNames.anchor (rr).pick (e).val,(e).property⟩:DescentSharedCableNames.Stage.Positive A)
local notation "site_" e => W.graph.src (parent_ e).val
local notation "sg_" e => (A).pos (site_ e)
local notation "where_" e => (hosts (sg_ e).2)
local notation "z_" e => ((A).block (site_ e),DescentSharedCableNames.Stage.outgoing A native S prior.valid (parent_ e),DescentCableDonorNames.role (e).val)

local notation "sampleSlot" => DescentRawCablePanel.slot A S prior.valid native hosts grp (rr).pick

theorem sample_original_seat (e : DescentRawCablePanel.Live A (rr).pick) :
    (groupSeat (sampleSlot e).2) = ((sg_ e).1,z_ e) :=by
  simp [DescentRawCablePanel.slot,groupSeat,Equiv.refl_apply]

include ticket named fit winner df order sumSize stored mounted birth in
/-- The receiver path selects the original host in the gathered window. The
packed native parts in that window are read directly, including the old
signed first-grain mark. All eight coordinates are genuine, even when the
source spatial rank, either endpoint serial, or old position is zero. -/
theorem occurrence_ticket {paths socketBits : ℕ} (p : Fin paths) (born : Bool)
    (e : DescentRawCablePanel.Live A (rr).pick) (socket_ : Cell socketBits)
    (pathHost : Fin paths→Fin port.hosts) (atHost : pathHost p=where_ e)
    (revs : Fin paths→Cell (DepotRAM.chartBits fmt)) (bit : 0 < bitsOut)
    (route : socket_.val=Ticket.socket p born (z_ e)) (priorRank xOld commonSerial actualPeer : ℕ) :
    let first:=decide (from_ ((rawGraph_).src e.val)=from_ ((rawGraph_).dst e.val))
    let final_:=decide (owner_ ((rawGraph_).src e.val)=owner_ ((rawGraph_).dst e.val))
    let second:=!first && final_
    let captured:=first.toNat≠0 ∨ second.toNat≠0
    let rawFields:=DepotRAM.Material.rawObserved fmt rawLayout (measured (where_ e) (sg_ e).1) (revs p) (z_ e)
    let part:=fun t=>measured (pathHost t) (sg_ e).1
    Ticket.current rawLayout part revs born (z_ e) socket_ priorRank xOld commonSerial actualPeer =
      ![if captured then (rawFields 4).val*r+(z_ e).1.val else 0,first.toNat,second.toNat,
        (DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role e.val) (decide ((parent_ e).val∈W.core))).toNat,
        if captured then 0 else commonSerial,if captured then 0 else actualPeer,
        (z_ e).2.1.val,(DescentCableDonorNames.role e.val).val] :=by
  intro first final_ second captured rawFields part
  have hit:=Ticket.at_socket (s:=fmt) p born (z_ e) socket_ rawLayout part revs priorRank xOld commonSerial actualPeer route
  dsimp only at hit
  have path_ : part p=measured (where_ e) (sg_ e).1:=by dsimp only [part];rw [atHost]
  rw [path_] at hit
  have fg:=posted_flags ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch bitsOut (revs p) bit e
  dsimp only at fg
  rw [sample_original_seat port e] at fg
  change (rawFields 2).val=first.toNat ∧ (rawFields 3).val=second.toNat at fg
  have mark : (rawFields 5).val=(decide ((parent_ e).val∈W.core)).toNat :=
    posted_anchor_mark port win hm profile dest issued roster pitch bitsOut (revs p) bit (parent_ e) (DescentCableDonorNames.role e.val)
  have signed : (if (DescentCableDonorNames.role e.val).val=0 then (rawFields 5).val else 1)=
    (DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role e.val) (decide ((parent_ e).val∈W.core))).toNat :=by
    by_cases atZero : (DescentCableDonorNames.role e.val).val=0 <;> simp [DescentOrdinarySignedMeta.markRole,atZero,mark]
  change Ticket.current rawLayout part revs born (z_ e) socket_ priorRank xOld commonSerial actualPeer=
    ![if (rawFields 2).val≠0 ∨ (rawFields 3).val≠0 then (rawFields 4).val*r+(z_ e).1.val else 0,
      (rawFields 2).val,(rawFields 3).val,if (DescentCableDonorNames.role e.val).val=0 then (rawFields 5).val else 1,
      if (rawFields 2).val≠0 ∨ (rawFields 3).val≠0 then 0 else commonSerial,
      if (rawFields 2).val≠0 ∨ (rawFields 3).val≠0 then 0 else actualPeer,
      (z_ e).2.1.val,(DescentCableDonorNames.role e.val).val] at hit
  simpa only [fg.1,fg.2,signed] using hit

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
