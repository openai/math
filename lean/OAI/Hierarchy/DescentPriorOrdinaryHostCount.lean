import OAI.Hierarchy.DescentOrdinaryDateVenue
import OAI.Hierarchy.DescentPriorResetArchive

namespace OAI
/-! # Retaining the original ordinary successor count across the entire date -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ) {w : ℕ}
  (input : Dated.Operands) (count : Bank) (wires : v.signed.Input) (B : StageVenueTail.Sources)
local notation "first" => v.donorEnd floor
local notation "mat" => v.materialEnd floor
local notation "peer" => v.peerTail floor
local notation "marked" => v.markEnd floor
local notation "sign" => v.signedEnd floor
local notation "doneArgs" => v.endAddress floor
local notation "raster" => v.rasterEnd floor
local notation "nodes" => v.operandEnd floor
local notation "stop" => v.primitiveEnd floor
local notation "old" => (⟨count,input.roster,input.hubs⟩:DescentOrdinaryVenueReturn.Sources)
local notation "hosts" => DescentOrdinaryVenueReturn.phase old mat v.k v.area.H v.area.D v.venue.hosts v.venue.degree w
local notation "coded" => v.signed.phase wires marked w

variable (s : ResultSteps w) (bank : v.ResultRoom floor B w)
def afterPeerTail :=
  (((((v.mark floor input w).seq coded).seq s.arguments).seq s.paid).seq (v.returnPhase floor B w bank)).seq s.primitive

theorem after_peer_span (ok : v.ResultRuns floor input count wires s) :
    Span (v.afterPeerTail floor input wires B s bank) peer stop :=by
  have bits : Span (v.mark floor input w) peer marked:=⟨v.markShape.low _,v.mark_any floor input ok.mark⟩
  have hs : Span coded marked sign:=by
    refine ⟨v.signed.room _,?_⟩
    intro m
    have mapped:=v.signed.calibrated marked
    have actual:=v.signed.phase_any wires marked w m ok.signed (mapped.le.trans_lt ok.signedRoom)
    exact ⟨actual.1,fun j h=>actual.2.1 j (h.imp_right (fun t=>mapped.le.trans t))⟩
  have hl : raster≤ nodes:=by
    have a : raster≤ v.metaStart floor:=by change raster≤ v.venue.endAddress raster;rw [v.venue.translates];omega
    have b : v.metaStart floor≤ v.metaEnd floor:=by rw [metaEnd,v.metadata.ordinary_translate];omega
    have c : v.metaEnd floor≤ nodes:=by rw [operandEnd,v.operandBook.affine];omega
    exact a.trans (b.trans c)
  exact (((((bits.join hs).join ok.arguments).join ok.funded).join
    ⟨hl,v.returnPhase_run floor B w bank⟩).join ok.primitive)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
open scoped Fin.CommRing
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (root shelf header : ℕ)
  (input : Dated.Operands) (count : Bank) (wires : v.signed.Input) (B : StageVenueTail.Sources)
  {w : ℕ} (s : ResultSteps w) (bank : v.ResultRoom (v.stageStart root) B w) (d : DonorDate) (positive : 0< d.exponent)
local notation "floor" => v.stageStart root
local notation "lay" => d.schedule v.payload v.seats v.bitsPerField
local notation "rot" => (lay).rotationEnd input.roster floor
local notation "measure" => (⟨v.prior.placement.wire,v.prior.placement.z,v.prior.placement.hist⟩:Dated.Measures)
local notation "src" => (⟨count,input.roster,input.hubs⟩:DescentOrdinaryVenueReturn.Sources)
local notation "meter" => d.counter v.payload rot header
local notation "meterEnd" => (meter).endAddr
local notation "vbase" => v.rasterEnd floor
local notation "ready" => v.metaStart floor
local notation "args" => v.venue.operands B vbase
variable (fit : Room v root shelf header input count wires s d)

def peerEntry (m : Memory w) : Memory w :=
  let t:=(v.archivePhase root shelf w).image m
  let t:=((lay).nativePhase v.gadget positive input measure w floor fit.matcher).image t
  let t:=(d.afterMatcher v.payload v.seats input v.bitsPerField floor w).image t
  let t:=(v.beforeSignedMaterial floor s.parts s.adjacency w).image t
  t

def afterPeer (m : Memory w) : Memory w :=
  (DescentOrdinaryVenueReturn.phase src (v.materialEnd floor) v.k v.area.H v.area.D v.venue.hosts v.venue.degree w).image (v.peerEntry root shelf header input count wires s d positive fit m)

theorem date_peer_read (m : Memory w) {x : ℕ} (peer : x < v.peerTail floor)
    (lateWord : meterEnd ≤ x) (away : x≠header) :
    v.dateOutput root shelf header input count wires B s bank d positive fit m x=
      v.afterPeer root shelf header input count wires s d positive fit m x :=by
  let prev:=v.afterPeer root shelf header input count wires s d positive fit m
  let tail:=v.afterPeerTail floor input wires B s bank
  have h:=v.after_peer_span floor input count wires B s bank fit.late
  have cheap:=(v.counter_run floor (tail.image prev) fit.topology fit.limit).2 x (.inl (peer.trans_le h.1))
  exact ((meter).counter_frame _ fit.counter x away (.inr lateWord)).trans (cheap.trans ((h.2 prev).2 x (.inl peer)))

include bank fit in
/-- The one-word common-host count is below the following date floor. -/
theorem ordinary_count_room : (PriorResetArchive.ordinary v floor).count.Fits w (v.fullEnd root) :=by
  have before : (PriorResetArchive.ordinary v floor).count.base < v.peerTail floor:=by
    change (DescentOrdinaryPeerCount.newCount _ _ _ _ _).base < DescentOrdinaryVenueReturn.roof _ _ _ _ _
    unfold DescentOrdinaryVenueReturn.roof DescentOrdinaryVenueReturn.hubs DescentOrdinaryVenueReturn.bookStart
      DescentOrdinaryPeerCount.newCount DescentOrdinaryPeerCount.roof
    dsimp only
    omega
  have inside:=before.trans_le (v.after_peer_span floor input count wires B s bank fit.late).1
  have stop : v.primitiveEnd floor ≤ v.fullEnd root := by
    change _ ≤ v.primitiveEnd floor + 2^v.countBits + v.area.batch + 1
    exact ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ 1)
  have small:=inside.trans_le stop
  have word:=small.trans fit.limit
  change 0<1 ∧ 1<2^w ∧ _+1 ≤ v.fullEnd root
  have more : 0<(PriorResetArchive.ordinary v floor).count.base:=by
    change 0 < DescentOrdinaryPeerRows.endAddress _ _ _ _ _
    unfold DescentOrdinaryPeerRows.endAddress DescentOrdinaryPeerChart.top
    have bump:=DescentDyadicSpan.span_pos (v.venue.hosts*v.venue.degree)
    omega
  omega

/-- The original roster/count scan runs before the per-host hub table. All
newly materialized argument, payload, primitive, and meter words leave this address readable. -/
theorem date_host_count (m : Memory w) {N : ℕ}
    (afterMeter : meterEnd≤(PriorResetArchive.ordinary v floor).count.base)
    (headerLow : header < meterEnd)
    (readCount : v.afterPeer root shelf header input count wires s d positive fit m
      (PriorResetArchive.ordinary v floor).count.base=(N:Word w)) :
    v.dateOutput root shelf header input count wires B s bank d positive fit m
      (PriorResetArchive.ordinary v floor).count.base=(N:Word w) :=by
  apply Eq.trans (v.date_peer_read root shelf header input count wires B s bank d positive fit m _ afterMeter
    (ne_of_gt (headerLow.trans_le afterMeter))) readCount
  change (DescentOrdinaryPeerCount.newCount _ _ _ _ _).base < DescentOrdinaryVenueReturn.roof _ _ _ _ _
  unfold DescentOrdinaryVenueReturn.roof DescentOrdinaryVenueReturn.hubs DescentOrdinaryVenueReturn.bookStart
    DescentOrdinaryPeerCount.newCount DescentOrdinaryPeerCount.roof
  dsimp only
  omega

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
