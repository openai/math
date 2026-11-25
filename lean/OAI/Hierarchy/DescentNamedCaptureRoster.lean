import OAI.Hierarchy.DescentNamedMatrixPorts
import OAI.Hierarchy.DescentNamedOriginalRootBanks
import OAI.Hierarchy.DescentCalendarCapturedRoots
import OAI.Hierarchy.DescentNamedResetRootPagesFit

namespace OAI
/-! # The unpadded prior roster at the actual classified successor memory -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks

theorem roster_after_cap_cast {D k n a b : ℕ} (eqn : a=b) (old : EarlierBanks D k a n) :
    ((congrArg (fun c=>EarlierBanks D k c n) eqn).mp old).oldRoster=old.oldRoster:=by
  subst b
  rfl

end Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
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
  (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "date₀" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "nextCPU" => (date₀).successor
local notation "start" => (date₀).stageStart floor
local notation "base₀" => (date₀).rebased start
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
local notation "rc" => (date₀).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (date₀).stencilPhase sh start count io.hubs g (2^n)
local notation "E" => (date₀).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (nextCPU).middle.stop base₀
local notation "early" => (nextCPU).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (nextCPU).front.SceneRoom early ((nextCPU).issuedScene base₀ older) w)
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


private theorem named_roster_address : (u).earlier.oldRoster=(atlas).directions.roster:=by
  change (older).oldRoster=(atlas).directions.roster
  have half : (date₀).c/2=cap := by change (2*cap)/2=cap; omega
  unfold namedOriginals CandidateFront.calendarOriginals
  exact CandidateFront.EarlierBanks.roster_after_cap_cast (D:=venue.degree) (k:=k) (n:=n) half _

/-- The original calibrated sender and the joint lookup read the same old roster on
every padded row. The receiver and the classifier both preserve its actual words. -/
theorem DateInputs.fromNamed_capture_roster
    (degreeAt : venue.degree=D) (ready : (u).Ready) (mem measured classified : Memory w)
    (seen : stageVenue input input.valid.host io (nextCPU).funded.oldLanes (nextCPU).funded.precision floor
      (input.venueRoster input.valid.host) mem) (kept : ∀x<floor,measured x=mem x)
    (μ : DescentGL.Layout (E).dim) (order : (P).S.OldOrder (P).X (P).base (P).bank g
      (B).terminals.commonDepth μ measured)
    (lower : ∀x,x<actorBase→classified x=(rc).preparedImage book prepared measured x) :
    (u).earlier.oldRoster.Fits w actorBase ∧ HH*input.placement.degree≤(u).earlier.oldRoster.size ∧
    ∀(a:Fin HH) (j:Fin input.placement.degree),classified
      ((u).earlier.oldRoster.base+(a.val*input.placement.degree+j.val))=
      (target (DescentPacking.PackedMatch.Local.Stage.hostRotor idx (DescentGroupPeerOrder.hostRoster input.placement
        ((idx).trans Fin.valEmbedding)) a j):Word w):=by
  have same : (u).earlier.oldRoster=(atlas).directions.roster:=by
    apply named_roster_address
  rw [same]
  have accessible : Accessible (atlas).directions ((ly).source (P).S.r) HH (2^cc) (2^e) w sep :=
    Atlas.accessible_sameDegree rfl _ _ order.accessible
  have sepProj : sep≤(rc).projectionEnd := ((P).S.header_before_output (P).base).trans (rc).origin_le_projection
  have late : (rc).projectionEnd≤actorBase:=by
    rw [←ready.rootEnd]
    obtain ⟨l₁,l₂,l₃⟩:=(book).limits (rc).projectionEnd HH (2^cc) (2^e)
    exact (l₁.trans (l₂.trans l₃)).trans (show (rc).headerEnd book≤(rc).preparedEnd book from Nat.le_add_right ..)
  have sepActor:=sepProj.trans late
  have old:=(DateInputs.fromNamed_matrix_ports (B:=B) (ctl:=ctl) (p:=p)
    drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil
    fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom degreeAt ready mem measured
    seen kept μ order).1
  have degreeEq : input.placement.degree=venue.degree:=input.branch.trans degreeAt.symm
  refine ⟨⟨accessible.roster.1,accessible.roster.2.1,accessible.roster.2.2.trans sepActor⟩,
    degreeEq.symm ▸ accessible.rosterRoom,?_⟩
  intro a j
  let t:=j.cast degreeEq
  have offset : a.val*venue.degree+t.val<HH*venue.degree:=
    (Nat.add_lt_add_left t.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ a.isLt)
  let loc:=(atlas).directions.roster.base+(a.val*venue.degree+t.val)
  have addr : loc<sep:=(Nat.add_lt_add_left (offset.trans_le accessible.rosterRoom) _).trans_le accessible.roster.2.2
  have word : classified loc = (rc).preparedMid book prepared measured loc :=
    (lower loc (addr.trans_le sepActor)).trans (((rc).prepared_window book prepared measured loc
      (addr.trans_le sepProj)).trans ((rc).prepared_mid_window book prepared measured loc (addr.trans_le sepProj)).symm)
  have addrEq : (atlas).directions.roster.base+(a.val*input.placement.degree+j.val)=loc:=by
    simp only [loc,t,Fin.val_cast,degreeEq]
  have peerEq : input.venueRoster input.valid.host a (Fin.cast degreeAt t)=
      DescentPacking.PackedMatch.Local.Stage.hostRotor idx (DescentGroupPeerOrder.hostRoster input.placement
        ((idx).trans Fin.valEmbedding)) a j:=by
    unfold Reached.venueRoster
    congr 1
  rw [addrEq]
  exact (word.trans (old.roster a t)).trans (congrArg (fun z=>(target z:Word w)) peerEq)


end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
