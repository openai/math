import OAI.Hierarchy.DescentNamedPacketRankEntry
import OAI.Hierarchy.DescentNamedMatrixPorts
import OAI.Hierarchy.DescentNamedResetRootPagesFit
import OAI.Hierarchy.DescentNamedSceneStemRoom

namespace OAI
/-! # Physical ID, venue and address reads on entry to original packet ranking -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver


namespace IndexedRoots
variable {D cap N n r c H G K R M hm lb tiny field Ht w : ℕ}
  {D' cap' n' r' c' H' G' Ht' : ℕ}
variable (x : IndexedRoots D cap N n r c H G K R M hm lb tiny field Ht w)
  (degree : D=D') (capacity : cap=cap') (dimension : n=n') (residual : r=r')
  (depth : c=c') (hosts : H=H') (groups : G=G') (height : Ht=Ht')


theorem preparedEnd_reindex :
    let y:=x.reindex degree capacity dimension residual depth hosts groups height
    y.receiver.preparedEnd y.book=x.receiver.preparedEnd x.book :=by
  subst_vars
  rfl
end IndexedRoots
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentPacking.PackedMatch.Local.Stage
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F X : Type} [Field F] {d : ℕ} {abits : X→ℕ} {W : MarkedWorld F d X abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤wide-k) (fitsSigned : e≤previous) (fitsCut : previous≤cc) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
local notation "E" => (a).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx
local notation "rawId" => (Z).rawHostRank T rank
local notation "HH" => S.hostSize age
local notation "nBits" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "tBits" => 2*k+n+2
local notation "amp" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap

open DescentFallbackPeriod.Projected DescentPaidResidentCount.Reset

open DescentPacking.PackedMatch.Local.Stage.Chooser
open DescentGL DescentPlainTerminal.Suffix
local notation "H₀" => (P).S.header (P).base
local notation "ly" => (P).S.chosen (P).base (P).bank (P).X.roster
local notation "roof" => (rc).headerEnd book
local notation "sep" => (P).S.afterHeader (P).base

variable (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
local notation "im" => fromNamed_root_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "middleBase" => (v).middle.stop base₀
local notation "directory" => (v).actor.endAddress middleBase
local notation "front" => (v).front

private theorem actor_base_before_end (setup : ActorSetup) (base : ℕ) : base ≤ setup.endAddress base := by
  obtain ⟨repeatAt,gateAt,outAt⟩ := setup.gate_order base
  have beforeRepeat : (setup.gate base).scalar ≤ (setup.gate base).repeatBase :=
    (Nat.le_add_right ..).trans repeatAt.le
  have beforeGate : (setup.gate base).repeatBase ≤ (setup.gate base).gateBase := by
    rw [←gateAt]
    unfold DescentSharedLeafLookup.Public.stop
    exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have beforeOutput : (setup.gate base).gateBase ≤ (setup.gate base).output :=
    (Nat.le_add_right ..).trans outAt.le
  exact (setup.scalar_before base).trans (beforeRepeat.trans (beforeGate.trans
    (beforeOutput.trans (Nat.le_add_right ..))))

theorem DateInputs.fromNamed_packet_intake (ready : (u).Ready) (mem measured : Memory w)
    (seen : stageVenue input input.valid.host io (v).funded.oldLanes (v).funded.precision floor
      (input.venueRoster input.valid.host) mem)
    (μ : DescentGL.Layout (E).dim)
    (order : (P).S.OldOrder (P).X (P).base (P).bank g (T).commonDepth μ measured) :
    (atlas).hostIndex.Fits w (im).receiver.origin ∧
    HH*chunks (2^(T).commonDepth) (2^e) ≤ (atlas).hostIndex.size ∧
    (∀q₀ : Row HH (2^(T).commonDepth) (2^e),measured ((atlas).hostIndex.base+(row _ _ _ q₀).val)=(q₀.1.val:Word w)) ∧
    (im).receiver.preparedEnd (im).book ≤ directory ∧
    io.hubs.Fits w directory ∧ HH ≤ io.hubs.size ∧ (front).oldKeys early < 2^w :=by
  have beforeMiddle:=named_root_prepared_end G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
  have same:=fromNamed_root_state (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt measured
  have upper : (im).receiver.preparedEnd (im).book=(rc).preparedEnd book:=by
    unfold fromNamed_root_image
    apply Receiver.IndexedRoots.preparedEnd_reindex
  have directoryAfter : middleBase ≤ directory := actor_base_before_end ..
  have sourceAfter : floor ≤ directory :=by
    obtain ⟨low,tokens,enter⟩:=(a).ingress.order floor
    obtain ⟨shelf,clip,_⟩:=(a).occupied start
    have startsAfter : floor ≤ base₀ :=(low.trans (tokens.trans enter)).trans (shelf.trans clip)
    have middleAfter : base₀ ≤ middleBase := by
      rw [(v).middle.translated]
      exact Nat.le_add_right ..
    exact startsAfter.trans (middleAfter.trans directoryAfter)
  have first : (atlas).hostIndex.Fits w sep :=((P).S.banks (P).X (P).base (P).bank ready.stencil.operands).1
  have low : sep ≤ (rc).origin :=(P).S.header_before_output (P).base
  have hubs:=seen.2.2.2.2.1
  have raw : (front).oldKeys early ≤ (front).rawTablesEnd early:=by
    rw [←(front).tables_end early sceneRoom.sameLanes,((front).rawTables early).end_eq]
    exact Nat.le_add_right ..
  refine ⟨?_,?_,?_,upper.le.trans (beforeMiddle.le.trans directoryAfter),
    ⟨hubs.1,hubs.2.1,hubs.2.2.trans sourceAfter⟩,seen.2.2.2.2.2.1,raw.trans_lt sceneRoom.evidenceFit⟩
  · rw [same.1]
    exact ⟨first.1,first.2.1,first.2.2.trans low⟩
  · rw [B.commonDepth]
    exact Nat.le_pow_clog (by decide) _
  · rw [B.commonDepth]
    exact ((H₀).addresses measured order.resident).1

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
