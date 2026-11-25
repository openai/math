import OAI.Hierarchy.DescentNamedOriginalHeader
import OAI.Hierarchy.DescentPackedMatchChooserFrame
import OAI.Hierarchy.DescentResetAtlasRoom

namespace OAI
/-! # Original peer and host reads across the chosen stencil's root preparation -/
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
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "nextCPU" => (a).successor
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

/-- The root prefix reads the original venue roster and the scalar host ID for each padded row. -/
theorem DateInputs.fromNamed_matrix_ports
    (degreeAt : venue.degree=D) (ready : (u).Ready) (mem measured : Memory w)
    (seen : stageVenue input input.valid.host io (nextCPU).funded.oldLanes (nextCPU).funded.precision floor
      (input.venueRoster input.valid.host) mem) (kept : ∀x<floor,measured x=mem x)
    (μ : DescentGL.Layout (E).dim) (order : (P).S.OldOrder (P).X (P).base (P).bank g (B).terminals.commonDepth μ measured) :
    let rs:=fun v j=>input.venueRoster input.valid.host v (Fin.cast degreeAt j)
    let mid:=(rc).preparedMid book prepared measured
    Mounted (atlas).directions rs mid (2^cc) (2^e) ∧
    Accessible (atlas).directions (atlas).hostIndex HH (2^cc) (2^e) w roof ∧
    ∀cell : Row HH (2^cc) (2^e),(Expr.lookup (atlas).hostIndex .row).eval mid
      ((row _ _ _ cell).val:Word w)=(cell.1.val:Word w) :=by
  intro rs mid
  have sepLow : sep≤(rc).origin :=(P).S.header_before_output (P).base
  have phaseRoom:=(P).S.banks (P).X (P).base (P).bank ready.stencil.operands
  have addr:=(order).accessible
  have accessible : Accessible (atlas).directions ((ly).source (P).S.r) HH (2^cc) (2^e) w sep :=
    Atlas.accessible_sameDegree rfl _ _ addr
  have original (v : Fin HH) (j : Fin venue.degree) :
      measured ((P).X.roster.base+(v.val*venue.degree+j.val))=(target (rs v j):Word w) :=by
    have ltt : v.val*venue.degree+j.val<HH*venue.degree := (Nat.add_lt_add_left j.isLt _).trans_le
      (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ v.isLt)
    have ll : v.val*D+(Fin.cast degreeAt j).val<HH*D :=by simpa only [←degreeAt,Fin.val_cast] using ltt
    have native:=seen.2.1.roster v (Fin.cast degreeAt j)
    have room:=seen.1.roster
    have top:= (Nat.add_lt_add_left (ll.trans_le seen.1.rosterRoom) _).trans_le room.2.2
    change measured (io.roster.base+(v.val*venue.degree+j.val))=_
    have addrEq : io.roster.base+(v.val*venue.degree+j.val)=
        io.roster.base+(v.val*D+(Fin.cast degreeAt j).val) := by simp only [Fin.val_cast,degreeAt]
    exact (congrArg measured addrEq).trans ((kept _ top).trans native)
  have warm : Mounted (atlas).directions rs measured (2^cc) (2^e) :=
    Atlas.mounted_sameDegree rfl _ rs measured (order.mounted rs original)
  have «prefix» (j : ℕ) (below : j<sep) : mid j=measured j :=
    ((rc).prepared_mid_window book prepared measured j ((below.trans_le sepLow).trans_le (rc).origin_le_projection)).trans
      (((rc).prefix_hardware prepared.toPrefixFits measured).2.2 j (.inl (below.trans_le sepLow)))
  have high : sep≤roof :=
    sepLow.trans ((rc).origin_le_projection.trans (by
      obtain ⟨l₁,l₂,l₃⟩:=(book).limits (rc).projectionEnd HH (2^cc) (2^e)
      exact l₁.trans (l₂.trans l₃)))
  have bank : (atlas).hostIndex.Fits w sep := phaseRoom.1
  have slots : HH*chunks (2^cc) (2^e) ≤ (atlas).hostIndex.size :=Nat.le_pow_clog (by decide) _
  have ace : Accessible (atlas).directions (atlas).hostIndex HH (2^cc) (2^e) w sep :=
    {accessible with source:=bank,srcRoom:=slots}
  refine ⟨mounted_before _ _ _ measured mid warm «prefix» accessible,accessible_before _ _ ace high,?_⟩
  intro z
  have entry:=(H₀).addresses measured order.resident
  have ix := (row HH (2^cc) (2^e) z).isLt.trans_le slots
  have small:= (Nat.add_lt_add_left ix _).trans_le bank.2.2
  exact (DescentPackedZip.bank_read _ mid ix bank).trans ((«prefix» _ small).trans (entry.1 z))

local notation "pg" => ((false,.inr (⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le k) (by decide)⟩,none)) : DescentSixParty.Chronology.RootPage k (2^n))
local notation "deckNow" => Receiver.IssuedDeck.mk (atlas).directions (atlas).board (atlas).primitive pg
local notation "wordMenu" dd => (deckNow).reindex dd rfl
  (show k=(cc-e+(e+k))-(T).commonDepth by rw [B.commonDepth];omega)
local notation "real" => PackedFlow.Padded.roster (D:=input.placement.degree) input.placement
  (ClosedReset.Recorded.oldName input) input.valid.host

theorem DateInputs.fromNamed_reached_ports
    (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap) (ready : (u).Ready) (mem measured : Memory w)
    (seen : stageVenue input input.valid.host io (nextCPU).funded.oldLanes (nextCPU).funded.precision floor
      (input.venueRoster input.valid.host) mem) (kept : ∀x<floor,measured x=mem x)
    (μ : DescentGL.Layout (E).dim) (order : (P).S.OldOrder (P).X (P).base (P).bank g (B).terminals.commonDepth μ measured) :
    let images:=fromNamed_matrix_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
    let desks:=wordMenu (degreeAt.trans input.branch.symm)
    let mid:=images.receiver.preparedMid images.book images.prepared measured
    Mounted desks.peers real mid (2^(T).commonDepth) (2^e) ∧
    Accessible desks.peers (atlas).hostIndex HH (2^(T).commonDepth) (2^e) w (images.receiver.headerEnd images.book) ∧
    ∀cell : Row HH (2^(T).commonDepth) (2^e),(Expr.lookup (atlas).hostIndex .row).eval mid
       ((row _ _ _ cell).val:Word w)=(cell.1.val:Word w) :=by
  intro images desks mid
  have state:=fromNamed_matrix_state (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt measured
  obtain ⟨mounted,accessible,ids⟩:=DateInputs.fromNamed_matrix_ports (B:=B) drift degree payload e previous
    M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom degreeAt ready mem measured seen kept μ order
  have port:=(deckNow).mounted (degreeAt.trans input.branch.symm) rfl
    (show k=(cc-e+(e+k))-(T).commonDepth by rw [B.commonDepth];omega) _ _ mounted
  have peq : (fun v j=>input.venueRoster input.valid.host v
      (((j : Fin input.placement.degree).cast (degreeAt.trans input.branch.symm).symm).cast degreeAt))=real :=by
    funext v j
    have namesEq : DescentResetSignedTokens.venueNames input = ClosedReset.Recorded.oldName input := by
      ext vertex
      rfl
    simpa only [Fin.cast_cast,namesEq] using DescentResetCanvasIngress.roster_at_degree input input.valid.host v j
  have mountedReal : Mounted desks.peers real ((rc).preparedMid book prepared measured) (2^cc) (2^e) :=
    (congrArg (fun rs => Mounted desks.peers rs ((rc).preparedMid book prepared measured) (2^cc) (2^e)) peq).mp port
  dsimp only [mid]
  rw [state.2.2.2.2.1,state.2.2.2.1]
  let atDepth (depth : ℕ) : Prop :=
    Mounted desks.peers real ((rc).preparedMid book prepared measured) (2^depth) (2^e) ∧
    Accessible desks.peers (atlas).hostIndex HH (2^depth) (2^e) w ((rc).headerEnd book) ∧
    ∀cell : Row HH (2^depth) (2^e),(Expr.lookup (atlas).hostIndex .row).eval ((rc).preparedMid book prepared measured)
      ((row _ _ _ cell).val:Word w)=(cell.1.val:Word w)
  have checked : atDepth cc := ⟨mountedReal,(deckNow).accessible _ rfl _ _ accessible,ids⟩
  exact (congrArg atDepth B.commonDepth.symm).mp checked



end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
