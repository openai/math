import OAI.Hierarchy.DescentNamedActorPanelFromVenue
import OAI.Hierarchy.DescentOriginalHeaderOnPublic
import OAI.Hierarchy.DescentIndexedRootState
import OAI.Hierarchy.DescentReindexedIssuedBook
import OAI.Hierarchy.DescentNamedMatrixPacketRoom

namespace OAI
/-! # The original root header from the named date's measured native memory -/
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
local notation "sources" => atlasSender atlas sh start count io.hubs g (2^n) roots w
local notation "middle" => (v).middle
local notation "X₀" => Receiver.IndexedRoots.mk (rc) (book) prepared (sources)
local notation "fac" => 32*Nat.clog 2 (2*venue.degree)
variable (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)

/-- Cast the receiver, its prepared book, and its actual source rows together to the reached reset. -/
def fromNamed_root_image :=
  (X₀).reindex (degreeAt.trans input.branch.symm)
    ((show (a).c/2=cap by change (2*cap)/2=cap;omega).trans capAt.symm) B.dimension.symm (ClosedReset.Window.calendar_residual B).symm
    B.commonDepth.symm rfl (S.group_power ctl.base ctl.radix age)
    (congrArg (fun j=>GroupStage.depthBound j n f g) degreeAt)
/-- The actual receiver first consumes the low and high chunks at their public sum width. -/
def fromNamed_matrix_image :=
  (X₀).reindex (degreeAt.trans input.branch.symm)
    ((show (a).c/2=cap by change (2*cap)/2=cap;omega).trans capAt.symm) rfl
    (show k=(cc-e+(e+k))-(T).commonDepth by rw [B.commonDepth];omega)
    B.commonDepth.symm rfl (S.group_power ctl.base ctl.radix age)
    (congrArg (fun j=>GroupStage.depthBound j n f g) degreeAt)
local notation "staged" => fromNamed_matrix_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "im" => fromNamed_root_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt

include fitsSigned fitsCut in
/-- The bit-width of the receiver’s two physical chunks is the measured transform dimension. -/
theorem fromNamed_matrix_width : cc-e+(e+k)=(Z).k :=by
  rw [B.keyWidth];omega

/-- Reading the original packet at the canonical width recovers the named root image. -/
theorem fromNamed_matrix_target :
    (staged).reindex rfl rfl B.dimension.symm
      (congrArg (fun width₁=>width₁-(T).commonDepth) (show cc-e+(e+k)=(Z).k by rw [B.keyWidth];omega))
      rfl rfl rfl rfl=im := by
  unfold fromNamed_matrix_image fromNamed_root_image
  apply Receiver.IndexedRoots.reindex_reindex

/-- These heterogeneous equalities compare data and programs before any execution. -/
theorem fromNamed_root_image_fields :
    HEq (im).receiver rc ∧ HEq (im).book book ∧ HEq (im).prepared prepared ∧ HEq (im).sources sources :=
  (X₀).reindex_fields ..

theorem fromNamed_root_state (measured : Memory w) :
    (im).receiver.origin=(rc).origin ∧ (im).receiver.saved=(rc).saved ∧ (im).receiver.stencil=(rc).stencil ∧
    (im).receiver.headerEnd (im).book=(rc).headerEnd book ∧
    (im).receiver.preparedMid (im).book (im).prepared measured=(rc).preparedMid book prepared measured ∧
    (im).receiver.preparedImage (im).book (im).prepared measured=(rc).preparedImage book prepared measured :=
  (X₀).unchanged (degreeAt.trans input.branch.symm)
    ((show (a).c/2=cap by change (2*cap)/2=cap;omega).trans capAt.symm) B.dimension.symm
    (ClosedReset.Window.calendar_residual B).symm B.commonDepth.symm rfl
    (S.group_power ctl.base ctl.radix age) (congrArg (fun j=>GroupStage.depthBound j n f g) degreeAt) measured

local notation "pg" => ((false,.inr (⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le k) (by decide)⟩,none)) : DescentSixParty.Chronology.RootPage k (2^n))
local notation "deckNow" => Receiver.IssuedDeck.mk (atlas).directions (atlas).board (atlas).primitive pg

/-- Actual board, role literals, and page selected by the named root program. -/
def fromNamed_root_menu :=
  (deckNow).reindex (degreeAt.trans input.branch.symm) B.dimension.symm (ClosedReset.Window.calendar_residual B).symm

local notation "menu" => (deckNow).reindex (degreeAt.trans input.branch.symm) B.dimension.symm (ClosedReset.Window.calendar_residual B).symm
/-- Both members reconstruct the issued native root book at the reached coordinate system. -/
theorem fromNamed_root_image_issued :
    (im).book=(im).receiver.issuedBook E (P).S (P).X (P).base (P).bank g (menu).peers (atlas).hostIndex
      (.lit ((a).c/2)) (a).depthCut (a).classBound (a).fullBudget (P).S.total (a).ports (menu).board (atlas).packet
      (atlas).C (atlas).groupDigits (atlas).batches (atlas).layerBits (atlas).factor (menu).primitive (menu).page ∧
    (im).sources=(im).receiver.atlasSources E (P).S (P).X (P).base (P).bank g (menu).peers (atlas).hostIndex
      (.lit ((a).c/2)) (a).depthCut (a).classBound (a).fullBudget (P).S.total (a).ports (menu).board (atlas).packet
      (atlas).C (atlas).groupDigits (atlas).batches (atlas).layerBits (atlas).factor (menu).primitive (menu).page := by
  exact Receiver.reindex_issued rc E (P).S (P).X (P).base (P).bank g (atlas).hostIndex (.lit ((a).c/2))
    (a).depthCut (a).classBound (a).fullBudget (P).S.total (a).ports (atlas).packet (atlas).C (atlas).groupDigits
    (atlas).batches (atlas).layerBits (atlas).factor deckNow prepared (degreeAt.trans input.branch.symm)
    ((show (a).c/2=cap by change (2*cap)/2=cap;omega).trans capAt.symm) B.dimension.symm
    (ClosedReset.Window.calendar_residual B).symm B.commonDepth.symm rfl (S.group_power ctl.base ctl.radix age)
    (congrArg (fun j=>GroupStage.depthBound j n f g) degreeAt)

set_option maxHeartbeats 900000 in
theorem fromNamed_root_image_calendar (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent) :
    (im).book=(im).receiver.issuedBook E (P).S (P).X (P).base (P).bank g (menu).peers (atlas).hostIndex
      (.lit input.placement.cap) f (quota S.rounds) (input.placement.wire*(input.placement.z*G.b)*input.placement.cap) (P).S.total (a).ports (Z).graph (Z).width
      C (atlas).groupDigits (atlas).batches (DescentRecordedRotorLayers.width f input.placement.cap) (atlas).factor (menu).primitive (menu).page ∧
    (im).sources=(im).receiver.atlasSources E (P).S (P).X (P).base (P).bank g (menu).peers (atlas).hostIndex
      (.lit input.placement.cap) f (quota S.rounds) (input.placement.wire*(input.placement.z*G.b)*input.placement.cap) (P).S.total (a).ports (Z).graph (Z).width
      C (atlas).groupDigits (atlas).batches (DescentRecordedRotorLayers.width f input.placement.cap) (atlas).factor (menu).primitive (menu).page :=by
  have got :=fromNamed_root_image_issued (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
  have preserved :=(deckNow).original (degreeAt.trans input.branch.symm) B.dimension.symm
    (ClosedReset.Window.calendar_residual B).symm
  have spell : (menu).board=(Z).graph :=eq_of_heq (preserved.2.1.trans B.graph.symm)
  have width : (atlas).packet=(Z).width :=B.width.symm
  have ratio : (a).c/2=input.placement.cap :=(show (a).c/2=cap by change (2*cap)/2=cap;omega).trans capAt.symm
  have rate : (a).fullBudget=input.placement.wire*(input.placement.z*G.b)*input.placement.cap :=by
    change S.epochPower^S.priceExponent*(S.grainAt G.b p (age+1)*G.b)*cap=_
    exact congrArg₂ Nat.mul
      (congrArg₂ Nat.mul (input.edges.trans fee).symm
        (congrArg (fun x : ℕ => x * G.b) (input.grain.trans gr).symm)) capAt.symm
  have layer : (atlas).layerBits=DescentRecordedRotorLayers.width f input.placement.cap  := by
    change DescentRecordedRotorLayers.width f ((a).c/2) = _
    exact congrArg (DescentRecordedRotorLayers.width f) ratio
  have depthEq : (a).depthCut = f := rfl
  have quotaEq : (a).classBound = quota S.rounds := rfl
  have tableEq : (atlas).C = C := rfl
  simp only [spell,width,ratio,rate,layer,depthEq,quotaEq,tableEq] at got
  exact got

local notation "wordMenu" => (deckNow).reindex (degreeAt.trans input.branch.symm) rfl
  (show k=(cc-e+(e+k))-(T).commonDepth by rw [B.commonDepth];omega)

/-- Both intermediate constructor projections still use the prechosen public bit-width sum. -/
theorem fromNamed_matrix_issued :
    (staged).book=(staged).receiver.issuedBook E (P).S (P).X (P).base (P).bank g (wordMenu).peers (atlas).hostIndex
      (.lit ((a).c/2)) (a).depthCut (a).classBound (a).fullBudget (P).S.total (a).ports (wordMenu).board (atlas).packet
      (atlas).C (atlas).groupDigits (atlas).batches (atlas).layerBits (atlas).factor (wordMenu).primitive (wordMenu).page ∧
    (staged).sources=(staged).receiver.atlasSources E (P).S (P).X (P).base (P).bank g (wordMenu).peers (atlas).hostIndex
      (.lit ((a).c/2)) (a).depthCut (a).classBound (a).fullBudget (P).S.total (a).ports (wordMenu).board (atlas).packet
      (atlas).C (atlas).groupDigits (atlas).batches (atlas).layerBits (atlas).factor (wordMenu).primitive (wordMenu).page :=by
  exact Receiver.reindex_issued rc E (P).S (P).X (P).base (P).bank g (atlas).hostIndex (.lit ((a).c/2))
    (a).depthCut (a).classBound (a).fullBudget (P).S.total (a).ports (atlas).packet (atlas).C (atlas).groupDigits
    (atlas).batches (atlas).layerBits (atlas).factor deckNow prepared (degreeAt.trans input.branch.symm)
    ((show (a).c/2=cap by change (2*cap)/2=cap;omega).trans capAt.symm) rfl
    (show k=(cc-e+(e+k))-(T).commonDepth by rw [B.commonDepth];omega) B.commonDepth.symm rfl (S.group_power ctl.base ctl.radix age)
    (congrArg (fun j=>GroupStage.depthBound j n f g) degreeAt)

theorem fromNamed_matrix_state (measured : Memory w) :
    (staged).receiver.origin=(rc).origin ∧ (staged).receiver.saved=(rc).saved ∧ (staged).receiver.stencil=(rc).stencil ∧
    (staged).receiver.headerEnd (staged).book=(rc).headerEnd book ∧
    (staged).receiver.preparedMid (staged).book (staged).prepared measured=(rc).preparedMid book prepared measured ∧
    (staged).receiver.preparedImage (staged).book (staged).prepared measured=(rc).preparedImage book prepared measured :=
  (X₀).unchanged (degreeAt.trans input.branch.symm)
    ((show (a).c/2=cap by change (2*cap)/2=cap;omega).trans capAt.symm) rfl
    (show k=(cc-e+(e+k))-(T).commonDepth by rw [B.commonDepth];omega) B.commonDepth.symm rfl
    (S.group_power ctl.base ctl.radix age) (congrArg (fun j=>GroupStage.depthBound j n f g) degreeAt) measured

theorem fromNamed_matrix_area (ready : (u).Ready)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(v).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w) :
    (staged).sources.OperandRoom HH (2^(T).commonDepth) (2^e) w ((staged).receiver.headerEnd (staged).book) :=by
  have limits:=chosen_root_pages_fit G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count chosen pitch small word ceiling
  have raw:=(atlas_geometry atlas sh start count io.hubs g (2^n) roots ready.stencil ready.prime.fit
    prepared.toPrefixFits limits.1 rfl rfl rfl rfl rfl limits.2).2
  have same:=fromNamed_matrix_state (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt (fun _=>0)
  rw [same.2.2.2.1]
  apply (X₀).room_at
  exact raw

theorem fromNamed_root_area (ready : (u).Ready)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(v).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w) :
    (im).sources.OperandRoom HH (2^(T).commonDepth) (2^e) w ((im).receiver.headerEnd (im).book) :=by
  have limits:=chosen_root_pages_fit G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count chosen pitch small word ceiling
  have raw:=(atlas_geometry atlas sh start count io.hubs g (2^n) roots ready.stencil ready.prime.fit
    prepared.toPrefixFits limits.1 rfl rfl rfl rfl rfl limits.2).2
  have same:=fromNamed_root_state (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt (fun _=>0)
  rw [same.2.2.2.1]
  apply (X₀).room_at
  exact raw

/-- The public book reads the measured roster and both funded width bounds on this run. -/
theorem DateInputs.fromNamed_original_header (ready : (u).Ready)
    (measured : Memory w)
    (observed : ClosedReset.Recorded.ActorPanelAt (B:=B) (M:=2^e) (t:=tBits) (nbits:=nBits)
      count (E).depthRows (rc).stencil book measured)
    (hubs : HH≤ io.hubs.size) (hosts : HH<2^w) (degFit : venue.degree+1<2^w)
    (names : DescentFallbackShapeTable.actorWordBits k fac g n≤w)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(v).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w) (capacity : venue.cap=cap)
    (heightBits : Ht+2≤w) :
    OriginalHeader B input.valid.host (im).receiver (im).book measured :=by
  have boundBegin : (P).base≤(rc).origin := ((P).S.banks (P).X (P).base (P).bank ready.stencil.operands).2.2.2.2.2.2.2.2.trans
    ((P).S.header_before_output (P).base)
  have carry {b : Bank} (before : b.Fits w (P).base) : b.Fits w (rc).origin :=
    ⟨before.1,before.2.1,before.2.2.trans boundBegin⟩
  have prior:=ready.stencil.operands.old
  have funds:=fromNamed_matrix_packing G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count chosen pitch small word ceiling capacity
  have paid : (a).c/2=venue.cap :=(show (a).c/2=cap by change (2*cap)/2=cap;omega).trans capacity.symm
  exact ClosedReset.original_header_on_public B X₀ (degreeAt.trans input.branch.symm)
    (paid.trans (capacity.trans capAt.symm)) B.dimension.symm (ClosedReset.Window.calendar_residual B).symm B.commonDepth.symm
    (S.group_power ctl.base ctl.radix age) (congrArg (fun j=>GroupStage.depthBound j n f g) degreeAt)
    count (E).depthRows (rc).stencil measured observed ⟨rfl,rfl,rfl,rfl⟩ (carry prior.roster) (carry prior.hubs)
    ready.stencil.operands.ports hubs hosts degFit (by omega) heightBits names (paid.symm ▸ funds.2.1) funds.2.2

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
