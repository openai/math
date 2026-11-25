import OAI.Hierarchy.DescentDatedIssuedOccurrenceTicket
import OAI.Hierarchy.DescentDatedTicketNativeSelect
import OAI.Hierarchy.DescentDatedReturnedTicketKey

namespace OAI
/-! # The actual native ticket pipeline on an issued original occurrence -/
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
set_option maxHeartbeats 1500000
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

open DescentDatedOperandReadPipeline
variable (geom : Geometry) (data : Data geom) (job : Fin geom.jobs) (h : Fin geom.hosts) (g : Fin geom.groups)
  (blocks : geom.blocks = 2^k) (cap : geom.cap = prior.placement.cap)
local notation "rkey" => rawKey geom data job h g
local notation "mat_" e => measured (where_ e) (sg_ e).1
local notation "reverse_" e => DescentHaloPackedRebase.digest (DepotRAM.Material.reverseEntries fmt roster (where_ e))

include named fit winner df order sumSize stored mounted birth in
theorem pipeline_occurrence_ticket (p : Fin geom.paths) (born : Bool) (e : DescentRawCablePanel.Live A (rr).pick)
    (bit : 0 < bitsOut) (room : breadth (A).degree ≤ 2^bitsOut)
    (listed : ∀v y,y∈(A).near v→∃j,roster (hosts v) j=some (hosts y))
    (agrees : ∀v j,roster (hosts v) j=canon (hosts v) j)
    (symmetric : ∀v v' j,roster v j=some v'→∃t,roster v' t=some v)
    (selected : Fin (geom.paths*(geom.blocks*(geom.cap*3))))
    (chosen : (anchorChoice geom data job h g).val=selected.val+1)
    (cause : (data.origin job 0 h g).val=if born then 2 else 1) (kind : (data.prior job 0 h g).val=1)
    (path : (if born then (data.origin job 1 h g).val+1 else (pathV geom data job 0 h g).val)=p.val+1)
    (mouth : born=true → (data.mouth job 1 h g).val=(z_ e).2.2.val)
    (matcher : ∀f : Fin 5,f.val≤2 ∨ f.val=4→(data.anchor job f selected h g).val=Ticket.anchor born (z_ e) f)
    (material : ∀f : Fin 6,2≤f.val → (data.raw job (f.castLE (by decide : 6≤8)) (rawCandidate geom (B:=2^k) (C:=prior.placement.cap) blocks cap p (z_ e)) h g).val=
      (DepotRAM.Material.rawObserved fmt rawLayout (mat_ e) (reverse_ e) (z_ e) f).val) :
    let idx:=rawCandidate geom (B:=2^k) (C:=prior.placement.cap) blocks cap p (z_ e)
    let first:=decide (from_ ((rawGraph_).src e.val)=from_ ((rawGraph_).dst e.val))
    let final_:=decide (owner_ ((rawGraph_).src e.val)=owner_ ((rawGraph_).dst e.val))
    let second:=!first && final_
    let captured:=first.toNat≠0 ∨ second.toNat≠0
    let halo:=DescentHaloCompilation.atSource (A).near hosts roster listed (A).pos (A).block prior.valid.coordinates own
    ∃inside : (site_ e) ∈ halo.member (local_ e),
      ticketAt geom data job h g =
        ![if captured then (halo.slot (local_ e) ⟨site_ e,inside⟩).val else 0,first.toNat,second.toNat,
          (DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role e.val) (decide ((parent_ e).val∈W.core))).toNat,
          if captured then 0 else (data.raw job 6 idx h g).val,if captured then 0 else (data.raw job 7 idx h g).val,
          (z_ e).2.1.val,(DescentCableDonorNames.role e.val).val] :=by
  intro idx first final_ second captured halo
  let state:Fin geom.paths→DepotRAM.Parts fmt:=fun _=>mat_ e
  let reverse:Fin geom.paths→Cell (DepotRAM.chartBits fmt):=fun _=>reverse_ e
  have anchor4 : (anchorV geom data job 4 h g).val=Ticket.anchor born (z_ e) 4:=
    (congrArg Fin.val (anchorV_at geom data job h g selected chosen 4)).trans (matcher 4 (Or.inr rfl))
  have route:=rawKey_at_socket geom data job h g (B:=2^k) (C:=prior.placement.cap) blocks cap p born (z_ e) cause path anchor4 mouth
  have read:=ticketAt_selected geom data job h g (s:=fmt) blocks cap p born (z_ e) rawLayout state reverse selected chosen route
    cause kind mouth (fun f hf=>matcher f (Or.inl hf)) material
  have original := focused_occurrence_ticket ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch bitsOut p born e rkey state reverse rfl rfl bit room listed agrees symmetric
    route (rankV geom data job 0 h g).val (data.origin job 2 h g).val
    (data.raw job 6 idx h g).val (data.raw job 7 idx h g).val
  obtain ⟨inside, receipt⟩ := original
  exact ⟨inside, read.trans receipt⟩

private theorem occurrence_name_lt {cap limit : ℕ} (ordinal : Fin cap) (role : Fin 11)
    (bound : 11 * cap ≤ limit) : 11 * ordinal.val + role.val < limit := by
  omega

include named fit winner df order sumSize stored mounted birth in
theorem resolved_occurrence_ticket (p : Fin geom.paths) (born : Bool) (e : DescentRawCablePanel.Live A (rr).pick)
    (bit : 0 < bitsOut) (room : breadth (A).degree ≤ 2^bitsOut)
    (listed : ∀v y,y∈(A).near v→∃j,roster (hosts v) j=some (hosts y))
    (agrees : ∀v j,roster (hosts v) j=canon (hosts v) j)
    (symmetric : ∀v v' j,roster v j=some v'→∃t,roster v' t=some v)
    (selected : Fin (geom.paths*(geom.blocks*(geom.cap*3))))
    (chosen : (anchorChoice geom data job h g).val=selected.val+1)
    (cause : (data.origin job 0 h g).val=if born then 2 else 1) (kind : (data.prior job 0 h g).val=1)
    (path : (if born then (data.origin job 1 h g).val+1 else (pathV geom data job 0 h g).val)=p.val+1)
    (mouth : born=true → (data.mouth job 1 h g).val=(z_ e).2.2.val)
    (matcher : ∀f : Fin 5,f.val≤2 ∨ f.val=4→(data.anchor job f selected h g).val=Ticket.anchor born (z_ e) f)
    (material : ∀f : Fin 6,2≤f.val → (data.raw job (f.castLE (by decide : 6≤8)) (rawCandidate geom (B:=2^k) (C:=prior.placement.cap) blocks cap p (z_ e)) h g).val=
      (DepotRAM.Material.rawObserved fmt rawLayout (mat_ e) (reverse_ e) (z_ e) f).val)
    (sources : Sources geom) {w₂ floor size : ℕ} (mem : Memory w₂)
    (records : Recorded geom sources data floor mem) (space : endAddress geom floor < 2^w₂)
    (positive : 0 < geom.lanes) (width : geom.resultBits*geom.lanes ≤ w₂) (sizeAt : geom.resultBits=size+2)
    (donorRoom : breadth (A).degree*r ≤ 2^(size+2)) (nameRoom : 11*(A).cap ≤ 2^(size+2))
    (prevPeer prevSerial piece : ℕ) (grain : Cell (size+2))
    (ptr : ∀f,(DescentOperandStateBanks.Pointer.cable prevPeer prevSerial piece).header f < 2^(size+2)) :
    let idx:=rawCandidate geom (B:=2^k) (C:=prior.placement.cap) blocks cap p (z_ e)
    let serial:=(data.raw job 6 idx h g).val
    let peer:=(data.raw job 7 idx h g).val
    let first:=decide (from_ ((rawGraph_).src e.val)=from_ ((rawGraph_).dst e.val))
    let final_:=decide (owner_ ((rawGraph_).src e.val)=owner_ ((rawGraph_).dst e.val))
    let second:=!first && final_
    let mark:=DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role e.val) (decide ((parent_ e).val∈W.core))
    let halo:=DescentHaloCompilation.atSource (A).near hosts roster listed (A).pos (A).block prior.valid.coordinates own
    let old:=(z_ e).2.1.val
    let role:=(DescentCableDonorNames.role e.val).val
    let key:=DescentPackedOperand.resolve (Ticket.compiled
      (readTicket geom sources (floor:=floor) mem job h g) grain (.cable prevPeer prevSerial piece) ptr)
    ∃inside : (site_ e) ∈halo.member (local_ e),let donor:=(halo.slot (local_ e) ⟨site_ e,inside⟩).val
      key=if first then DescentPackedOperand.Key.first donor 0 (11*old+role) piece
        else if second then DescentPackedOperand.Key.second donor 0 (11*old+role) piece
        else DescentPackedOperand.resolve (DescentPackedOperand.Public.fragment mark (peer:Cell (size+2))
          (serial:Cell (size+2)) (⟨piece,show piece<2^(size+2) from ptr 3⟩:Cell (size+2)) grain) :=by
  intro idx serial peer first final_ second mark halo old role key
  have receipt := pipeline_occurrence_ticket (F:=F) (P:=P) (d:=d) (bits:=bits) (G:=G)
    (S:=S) (q:=q) (ε:=ε) (k:=k) (i:=i) (z:=z) (D:=D) (wire:=wire) (hist:=hist) (w:=w)
    (short:=short) (a:=a) (W:=W) (prior:=prior) (he:=he) (choice:=choice) (n:=n)
    (z':=z') (D':=D') (next:=next) ticket port win hm named fit winner df order profile b m
    sumSize stored dest issued roster mounted birth pitch bitsOut geom data job h g blocks cap p born e bit room listed
    agrees symmetric selected chosen cause kind path mouth matcher material
  obtain ⟨inside, values⟩ := receipt
  refine ⟨inside,?_⟩
  intro donor
  have visible : ticketAt geom data job h g=postedVector donor first second mark serial peer old role:=
    values.trans (postedVector_eq donor first second mark serial peer old role).symm
  have donorFit : donor < 2^(size+2):=(halo.slot (local_ e) ⟨site_ e,inside⟩).isLt.trans_le donorRoom
  have nameFit : 11*old+role < 2^(size+2) :=
    occurrence_name_lt (z_ e).2.1 (DescentCableDonorNames.role e.val) nameRoom
  by_cases hit : first=true
  · have after_:second=false:=by simp [second,hit]
    simp only [hit,after_] at visible
    simpa only [hit, ite_true, Bool.false_eq_true, ite_false] using captured_physical geom data sources mem records space positive width job h g
      prevPeer prevSerial piece ptr grain sizeAt donor old role serial peer false mark visible donorFit nameFit
  · have noFirst:first=false:=Bool.eq_false_iff.mpr hit
    simp only [noFirst] at visible
    simp only [noFirst, Bool.false_eq_true, ite_false]
    cases after_:second with
    | true =>
      simp only [after_] at visible
      simpa using captured_physical geom data sources mem records space positive width job h g
        prevPeer prevSerial piece ptr grain sizeAt donor old role serial peer true mark visible donorFit nameFit
    | false =>
      simp only [after_] at visible
      simpa using survivor_physical geom data sources mem records space positive width job h g
        prevPeer prevSerial piece ptr grain sizeAt donor old role serial peer mark visible

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
