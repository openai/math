import OAI.Hierarchy.DescentDatedReturnedJobKey
import OAI.Hierarchy.DescentDatedNativeOccurrenceTicket

namespace OAI
/-! # Complete source-key classification from a physically selected cable occurrence -/
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

open DescentOperandStateBanks DescentDatedOperandReadPipeline DescentPackedOperand DescentDatedPriorOperand
variable (l:DescentDatedPriorOperand.Layout) (old:Books l) (typed:BookPointers old)
    (digits:Fin l.jobs→Fin l.hosts→Fin l.groups→Fin 8→ℕ) (grain:Cell (l.size+2))
local notation "side_" => fun j h y=>DescentDatedPublicGrain.withGrain grain (Ticket.recordedSide l.size (digits j h y))
local notation "role_" => fun j f h y=>Ticket.recordedRole l.size (digits j h y) f
variable (roleRoom:∀j h y,11*(Ticket.recordedRole l.size (digits j h y) 1).val+
    (Ticket.recordedRole l.size (digits j h y) 2).val<2^(l.size+2))
local notation "jobs_" => ofBooks old typed side_ role_ roleRoom

include ticket named fit winner df order sumSize stored mounted birth in
/-- Both old and newborn physical jobs feed their actual eight scalar values to the
same native typed resolver. The only chosen row is the specified raw occurrence. -/
theorem returned_cable_digits {paths socketBits:ℕ} (p:Fin paths) (born:Bool) (e:DescentRawCablePanel.Live A (rr).pick)
    (socket_:Cell socketBits) (route:socket_.val=Ticket.socket p born (z_ e))
    (bit:0<bitsOut) (room:breadth (A).degree≤2^bitsOut)
    (listed:∀v y,y∈(A).near v→∃j,roster (hosts v) j=some (hosts y))
    (agrees:∀v j,roster (hosts v) j=canon (hosts v) j)
    (symmetric:∀u v j,roster u j=some v→∃i,roster v i=some u)
    (j:Fin l.jobs) (h:Fin l.hosts) (y:Fin l.groups) (priorRank xOld serial peer:ℕ)
    (earned : digits j h y=Ticket.current rawLayout (fun _:Fin paths=>measured (where_ e) (sg_ e).1)
      (fun _:Fin paths=>DescentHaloPackedRebase.digest (DepotRAM.Material.reverseEntries fmt roster (where_ e)))
      born (z_ e) socket_ priorRank xOld serial peer) :
    let first:=decide (from_ ((rawGraph_).src e.val)=from_ ((rawGraph_).dst e.val))
    let final_:=decide (owner_ ((rawGraph_).src e.val)=owner_ ((rawGraph_).dst e.val))
    let second:=!first && final_
    let mark:=DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role e.val) (decide ((parent_ e).val∈W.core))
    let halo:=DescentHaloCompilation.atSource (A).near hosts roster listed (A).pos (A).block prior.valid.coordinates own
    let ordinal:=(z_ e).2.1.val
    let role:=(DescentCableDonorNames.role e.val).val
    ∃inside : (site_ e) ∈halo.member (local_ e),let donor:=(halo.slot (local_ e) ⟨site_ e,inside⟩).val
      digits j h y=postedVector donor first second mark serial peer ordinal role :=by
  intro first final_ second mark halo ordinal role
  let state : Fin paths → DepotRAM.Parts fmt := fun _ => measured (where_ e) (sg_ e).1
  let reverse : Fin paths → Cell (DepotRAM.chartBits fmt) := fun _ =>
    DescentHaloPackedRebase.digest (DepotRAM.Material.reverseEntries fmt roster (where_ e))
  have receipt := focused_occurrence_ticket (short:=short) (prior:=prior) (choice:=choice) (next:=next) ticket port win hm named fit winner df order profile b m sumSize
    stored dest issued roster mounted birth pitch bitsOut p born e socket_ state reverse rfl rfl bit room listed agrees
    symmetric route priorRank xOld serial peer
  obtain ⟨inside, values⟩ := receipt
  refine ⟨inside,?_⟩
  intro donor
  exact (earned.trans values).trans (postedVector_eq donor first second mark serial peer ordinal role).symm

include ticket named fit winner df order sumSize stored mounted birth in
theorem returned_cable_key {paths socketBits:ℕ} (p:Fin paths) (born:Bool) (e:DescentRawCablePanel.Live A (rr).pick)
    (socket_:Cell socketBits) (route:socket_.val=Ticket.socket p born (z_ e))
    (bit:0<bitsOut) (room:breadth (A).degree≤2^bitsOut)
    (listed:∀v y,y∈(A).near v→∃j,roster (hosts v) j=some (hosts y))
    (agrees:∀v j,roster (hosts v) j=canon (hosts v) j)
    (symmetric:∀u v j,roster u j=some v→∃i,roster v i=some u)
    (j:Fin l.jobs) (h:Fin l.hosts) (y:Fin l.groups) (priorRank xOld serial peer prevPeer prevSerial piece:ℕ)
    (read : ∀f,(booksHeader old j h y f).val=(Pointer.cable prevPeer prevSerial piece).header f)
    (earned : digits j h y=Ticket.current rawLayout (fun _:Fin paths=>measured (where_ e) (sg_ e).1)
      (fun _:Fin paths=>DescentHaloPackedRebase.digest (DepotRAM.Material.reverseEntries fmt roster (where_ e)))
      born (z_ e) socket_ priorRank xOld serial peer)
    (donors : breadth (A).degree*r≤2^(l.size+2)) (names : 11*(A).cap≤2^(l.size+2)) :
    let first:=decide (from_ ((rawGraph_).src e.val)=from_ ((rawGraph_).dst e.val))
    let final_:=decide (owner_ ((rawGraph_).src e.val)=owner_ ((rawGraph_).dst e.val))
    let second:=!first && final_
    let mark:=DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role e.val) (decide ((parent_ e).val∈W.core))
    let halo:=DescentHaloCompilation.atSource (A).near hosts roster listed (A).pos (A).block prior.valid.coordinates own
    let ordinal:=(z_ e).2.1.val
    let role:=(DescentCableDonorNames.role e.val).val
    let pieceFit:piece<2^(l.size+2):=(read 3).ge.trans_lt (booksHeader old j h y 3).isLt
    ∃inside : (site_ e) ∈halo.member (local_ e),let donor:=(halo.slot (local_ e) ⟨site_ e,inside⟩).val
      resolve (((jobs_) j).compiled h y)=if first then Key.first donor 0 (11*ordinal+role) piece
        else if second then Key.second donor 0 (11*ordinal+role) piece
        else resolve (Public.fragment mark (peer:Cell (l.size+2)) (serial:Cell (l.size+2)) ⟨piece,pieceFit⟩ grain) :=by
  intro first final_ second mark halo ordinal role pieceFit
  have receipt := returned_cable_digits (short:=short) (prior:=prior) (choice:=choice) (next:=next) ticket port win hm named fit winner df order profile b m sumSize
    stored dest issued roster mounted birth pitch bitsOut l digits p born e socket_ route bit room listed agrees symmetric
    j h y priorRank xOld serial peer earned
  obtain ⟨inside, values⟩ := receipt
  refine ⟨inside,?_⟩
  intro donor
  have nameFit : 11*ordinal+role < 2^(l.size+2) := by
    calc
      11*ordinal+role < 11*ordinal+11 := Nat.add_lt_add_left (DescentCableDonorNames.role e.val).isLt _
      _ = 11*(ordinal+1) := (Nat.mul_succ ..).symm
      _ ≤ 11*(A).cap := Nat.mul_le_mul_left 11 (z_ e).2.1.isLt
      _ ≤ _ := names
  exact returned_key l old typed digits grain roleRoom j h y prevPeer prevSerial piece read donor first second mark
    serial peer ordinal role (fun hf=>by simp [second,hf]) values
    ((halo.slot (local_ e) ⟨site_ e,inside⟩).isLt.trans_le donors) nameFit

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
