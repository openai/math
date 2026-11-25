import OAI.Hierarchy.DescentDatedRawCaptureFields

namespace OAI
/-! # Numeric ticket flags on the authentic predecessor and final owners -/
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
attribute [local irreducible] Stage.nativeParts physicalRows DepotRAM.chip packDonor StarKeys.nativeKey OrdinaryLink.donorKey OrdinaryLink.measuredDonors DepotRAM.Material.rawObserved
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
      let shape₀:=shape (2^k) prior.placement.degree (2*prior.placement.cap) profile
      let world:=terrain (short:=short) prior.placement (prior.order.trans Fin.valEmbedding)
        S prior.valid (cableNames k rankAt) win (rotor prior.placement rankAt)
      let partsAt:=spread (Equiv.refl (Fin (S.groupCount i))).toEmbedding port.vertex world
      let inputs:=Gather.flat (Gather.descriptorInputs (K:=2^(k+1)) shape₀ prior.placement.cap partsAt)
      ∀j : Fin (2^(k+1)*port.hosts * chunks (S.groupCount i) port.groupsPerWord),m (b+j.val)=((DescentPacking.PackedMatch.topologyWords (M:=port.groupsPerWord) shape₀ inputs j).val:Computability.VPVNP.BurstRAM.Word w))
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
    let shape₀:=shape (2^k) prior.placement.degree (2*limit) profile
    let cellAt:=DescentPacking.PackedMatch.Local.Stage.slot he prior.placement (Equiv.refl (Fin (S.groupCount i))).toEmbedding port.vertex hm
    ∀c : ScanColonies he stage,∀e : Matched flow limit (thinList actor tint c) (thickList actor tint c),
      ∃j : Fin shape₀.pairs,j.val=(pairNumber (DescentPacking.amount (live flow))
        (slabPacking flow limit (thinList actor tint c) (thickList actor tint c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=DescentPacking.PackedMatch.SixBirths.slot (cellAt c).2 j q
        DescentPacking.PackedMatch.SixBirths.atom stage.z (digit (shape₀.digit+1) ip.val (issued (dest+(cellAt c).1.val)).val) ip.val=
          some (stage.z,DescentTerminalEpochFlags.encode ((BitDescription.scannedRows he stage).profile choice ⟨c,e⟩),q.val))

variable (pitch bitsOut : ℕ)
    (rev : Cell (DepotRAM.chartBits (Stage.shapeOf (short:=short) prior.placement
      (donorNameBits prior.placement.stage.k prior.placement.stage.Δ))))
local notation "u" => rawFormat (G:=G) (prior:=prior) profile pitch bitsOut

local notation "sampleSlot" => DescentRawCablePanel.slot A S prior.valid native hosts grp (rr).pick
local notation:max "parts" h:arg j:arg => (measured h (groupSeat j).1)
local notation:max "read_" h:arg j:arg i:arg => DepotRAM.Material.rawObserved fmt u (parts h j) rev (groupSeat j).2 i

local notation "rawGraph_" => rawGraph he T choice
local notation "from_" => (originalId (((T).result he).state choice).graph.Site) ∘ rawInput he T choice ((rr).state choice)
local notation "owner_" => rawOwner he T choice n ((rr).state choice) (originalId _)


private theorem bit_val (c : Bool) (bit : 0 < bitsOut) : ((c.toNat:ℕ):Cell bitsOut).val=c.toNat :=by
  apply Fin.val_cast_of_lt
  cases c
  · exact Nat.two_pow_pos _
  · exact Nat.one_lt_two_pow (by omega)

include ticket named fit winner df order sumSize stored mounted birth in
theorem posted_flags (bit : 0 < bitsOut) (e : DescentRawCablePanel.Live A (rr).pick) :
    let s:=sampleSlot e
    let first:=decide (from_ ((rawGraph_).src e.val)=from_ ((rawGraph_).dst e.val))
    let kept:=decide (owner_ ((rawGraph_).src e.val)=owner_ ((rawGraph_).dst e.val))
    (read_ s.1 s.2 2).val=first.toNat ∧ (read_ s.1 s.2 3).val=(!first && kept).toNat :=by
  dsimp only
  have capture:=raw_capture_fields ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch bitsOut rev e
  exact ⟨(congrArg Fin.val capture.1).trans (bit_val bitsOut _ bit),(congrArg Fin.val capture.2).trans (bit_val bitsOut _ bit)⟩

include ticket named fit winner df order sumSize stored mounted birth in
theorem contracted_flags (bit : 0 < bitsOut) (e : DescentRawCablePanel.Live A (rr).pick)
    (collapsed : owner_ ((rawGraph_).src e.val)=owner_ ((rawGraph_).dst e.val)) :
    let s:=sampleSlot e
    let second:=decide (from_ ((rawGraph_).src e.val) ≠ from_ ((rawGraph_).dst e.val))
    (read_ s.1 s.2 2).val=(!second).toNat ∧ (read_ s.1 s.2 3).val=second.toNat :=by
  dsimp only
  have post:=posted_flags ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch bitsOut rev bit e
  by_cases priorEq : from_ ((rawGraph_).src e.val)=from_ ((rawGraph_).dst e.val) <;> simpa [priorEq,collapsed] using post

include ticket named fit winner df order sumSize stored mounted birth in
theorem uncontracted_flags (bit : 0 < bitsOut) (e : DescentRawCablePanel.Live A (rr).pick)
    (separate : from_ ((rawGraph_).src e.val) ≠ from_ ((rawGraph_).dst e.val))
    (remains : owner_ ((rawGraph_).src e.val) ≠ owner_ ((rawGraph_).dst e.val)) :
    let s:=sampleSlot e
    (read_ s.1 s.2 2).val=0 ∧ (read_ s.1 s.2 3).val=0 :=by
  have post:=posted_flags ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch bitsOut rev bit e
  dsimp only at post
  exact ⟨post.1.trans (by simp only [decide_eq_false separate,Bool.toNat_false]),
    post.2.trans (by simp only [decide_eq_false separate,decide_eq_false remains,Bool.not_false,Bool.and_false,Bool.toNat_false])⟩

theorem posted_anchor_mark (bit : 0 < bitsOut) (e : DescentSharedCableNames.Stage.Positive A) (role : Fin 11) :
    let src:=W.graph.src e.val
    let z:=(A).pos src
    let t:=DescentSharedCableNames.Stage.outgoing A native S prior.valid e
    (DepotRAM.Material.rawObserved fmt u (measured (hosts z.2) z.1) rev ((A).block src,t,role) 5).val=
      (decide (e.val∈W.core)).toNat :=
  (congrArg Fin.val (raw_anchor_core port win hm profile dest issued roster pitch bitsOut rev e role)).trans (bit_val bitsOut _ bit)

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
