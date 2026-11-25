import OAI.Hierarchy.DescentDatedOccurrenceTicket
import OAI.Hierarchy.DescentDatedRawDonorMembership

namespace OAI
/-! # All eight fields of the genuine ordinary ticket in the old donor chart -/
namespace Hierarchy.DescentDatedOperandCoordinates.Ticket
open DescentSIMDLookup DescentRawCablePanel DescentRawCablePanel.DepotRAM
open DescentRawCablePanel.DepotRAM.Material
open scoped Fin.CommRing
theorem socket_read_congr {s : DepotRAM.Shape} {P d : ℕ}
    (p : Fin P) (birth : Bool) (z : Seat s) (q : Cell d) (u : Setup)
    (state state' : Fin P→Parts s) (rev rev' : Fin P→Cell (chartBits s))
    (rank block start peer : ℕ) (route : q.val=socket p birth z)
    (state_at : state p=state' p) (rev_at : rev p=rev' p) :
    current u state rev birth z q rank block start peer =
      current u state' rev' birth z q rank block start peer := by
  have left := at_socket p birth z q u state rev rank block start peer route
  have right := at_socket p birth z q u state' rev' rank block start peer route
  exact left.trans ((by simpa only [state_at,rev_at] using right.symm) : _ = _)
end Hierarchy.DescentDatedOperandCoordinates.Ticket

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

local notation "canon" => hostRotor hosts (DescentGroupPeerOrder.hostRoster A ((hosts).trans Fin.valEmbedding))
local notation "own" => StarKeys.nativeKey W.graph W.core home color (T).cap addr ticket.donorChart.same lay
local notation "packs" => coloredPack W.graph W.core home color (A).cap
local notation "local_" e => newSite W.graph (rr).pick lay packs (GadgetNetwork.source W.graph (e).val)

include named fit winner df order sumSize stored mounted birth in
theorem issued_occurrence_ticket {paths socketBits : ℕ} (p : Fin paths) (born : Bool)
    (e : DescentRawCablePanel.Live A (rr).pick) (socket_ : Cell socketBits)
    (pathHost : Fin paths→Fin port.hosts) (atHost : pathHost p=where_ e)
    (bit : 0 < bitsOut) (room : breadth (A).degree ≤ 2^bitsOut)
    (listed : ∀v y,y∈(A).near v→∃j,roster (hosts v) j=some (hosts y))
    (agrees : ∀v j,roster (hosts v) j=canon (hosts v) j)
    (symmetric : ∀v v' j,roster v j=some v'→∃t,roster v' t=some v)
    (route : socket_.val=Ticket.socket p born (z_ e)) (priorRank xOld commonSerial actualPeer : ℕ) :
    let first:=decide (from_ ((rawGraph_).src e.val)=from_ ((rawGraph_).dst e.val))
    let final_:=decide (owner_ ((rawGraph_).src e.val)=owner_ ((rawGraph_).dst e.val))
    let second:=!first && final_
    let captured:=first.toNat≠0 ∨ second.toNat≠0
    let part:=fun t=>measured (pathHost t) (sg_ e).1
    let revs:=fun t=>DescentHaloPackedRebase.digest (DepotRAM.Material.reverseEntries fmt roster (pathHost t))
    let halo:=DescentHaloCompilation.atSource (A).near hosts roster listed (A).pos (A).block prior.valid.coordinates own
    ∃inside : (site_ e) ∈ halo.member (local_ e),
      Ticket.current rawLayout part revs born (z_ e) socket_ priorRank xOld commonSerial actualPeer =
        ![if captured then (halo.slot (local_ e) ⟨site_ e,inside⟩).val else 0,first.toNat,second.toNat,
          (DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role e.val) (decide ((parent_ e).val∈W.core))).toNat,
          if captured then 0 else commonSerial,if captured then 0 else actualPeer,
          (z_ e).2.1.val,(DescentCableDonorNames.role e.val).val] :=by
  intro first final_ second captured part revs halo
  have inside : (site_ e) ∈halo.member (local_ e):=
    Stage.raw_donor_membership A native S prior.valid rank win he prior.valid.coordinates named fit winner df order
      profile ticket.donorChart.same lay hosts roster listed e
  refine ⟨inside,?_⟩
  let rawFields:=DepotRAM.Material.rawObserved fmt rawLayout (measured (where_ e) (sg_ e).1) (revs p) (z_ e)
  have donor : (rawFields 4).val*r+(z_ e).1.val=(halo.slot (local_ e) ⟨site_ e,inside⟩).val :=by
    let location (receiver : Fin port.hosts) :=
      (DepotRAM.Material.rawObserved fmt rawLayout (measured (where_ e) (sg_ e).1)
        (DescentHaloPackedRebase.digest (DepotRAM.Material.reverseEntries fmt roster receiver)) (z_ e) 4).val*r+(z_ e).1.val
    change location (pathHost p)=_
    refine (congrArg location atHost).trans ?_
    exact Stage.original_capture_donor A native S prior.valid grp hosts win he hm profile dest issued (A).hub lay bytes
      (2^(packExponent 20 (T).Δ)+2) prior.valid.coordinates named fit winner df order ticket.donorChart.same roster listed agrees mounted symmetric
      e pitch bitsOut room
  have read:=occurrence_ticket ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch bitsOut p born e socket_ pathHost atHost revs bit route priorRank xOld commonSerial actualPeer
  change Ticket.current rawLayout part revs born (z_ e) socket_ priorRank xOld commonSerial actualPeer =
    ![if captured then (rawFields 4).val*r+(z_ e).1.val else 0,first.toNat,second.toNat,
      (DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role e.val) (decide ((parent_ e).val∈W.core))).toNat,
      if captured then 0 else commonSerial,if captured then 0 else actualPeer,
      (z_ e).2.1.val,(DescentCableDonorNames.role e.val).val] at read
  simpa only [donor] using read

include named fit winner df order sumSize stored mounted birth in
theorem focused_occurrence_ticket {paths socketBits : ℕ} (p : Fin paths) (born : Bool)
    (e : DescentRawCablePanel.Live A (rr).pick) (socket_ : Cell socketBits)
    (state : Fin paths→DepotRAM.Parts fmt) (reverse : Fin paths→Cell (DepotRAM.chartBits fmt))
    (stateAt : state p=measured (where_ e) (sg_ e).1)
    (reverseAt : reverse p=DescentHaloPackedRebase.digest (DepotRAM.Material.reverseEntries fmt roster (where_ e)))
    (bit : 0 < bitsOut) (room : breadth (A).degree ≤ 2^bitsOut)
    (listed : ∀v y,y∈(A).near v→∃j,roster (hosts v) j=some (hosts y))
    (agrees : ∀v j,roster (hosts v) j=canon (hosts v) j)
    (symmetric : ∀v v' j,roster v j=some v'→∃t,roster v' t=some v)
    (route : socket_.val=Ticket.socket p born (z_ e)) (priorRank xOld commonSerial actualPeer : ℕ) :
    let first:=decide (from_ ((rawGraph_).src e.val)=from_ ((rawGraph_).dst e.val))
    let final_:=decide (owner_ ((rawGraph_).src e.val)=owner_ ((rawGraph_).dst e.val))
    let second:=!first && final_
    let captured:=first.toNat≠0 ∨ second.toNat≠0
    let halo:=DescentHaloCompilation.atSource (A).near hosts roster listed (A).pos (A).block prior.valid.coordinates own
    ∃inside : (site_ e) ∈ halo.member (local_ e),
      Ticket.current rawLayout state reverse born (z_ e) socket_ priorRank xOld commonSerial actualPeer =
        ![if captured then (halo.slot (local_ e) ⟨site_ e,inside⟩).val else 0,first.toNat,second.toNat,
          (DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role e.val) (decide ((parent_ e).val∈W.core))).toNat,
          if captured then 0 else commonSerial,if captured then 0 else actualPeer,
          (z_ e).2.1.val,(DescentCableDonorNames.role e.val).val] :=by
  intro first final_ second captured halo
  have issuedRead:=issued_occurrence_ticket ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch bitsOut p born e socket_ (fun _=>where_ e) rfl bit room listed agrees symmetric
    route priorRank xOld commonSerial actualPeer
  obtain ⟨inside,read⟩ := issuedRead
  refine ⟨inside,?_⟩
  have same := Ticket.socket_read_congr p born (z_ e) socket_ rawLayout
    state (fun _ : Fin paths => measured (where_ e) (sg_ e).1)
    reverse (fun _ : Fin paths => DescentHaloPackedRebase.digest (DepotRAM.Material.reverseEntries fmt roster (where_ e)))
    priorRank xOld commonSerial actualPeer route stateAt reverseAt
  exact same.trans read

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
