import OAI.Hierarchy.DescentNamedResetDateInputs
import OAI.Hierarchy.DescentNamedResetRootPagesFit
import OAI.Hierarchy.DescentResetPrivateRootAddress

namespace OAI
/-! # The named reset reads the original physical private-page bank -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks

theorem root_after_cap_cast {D k n a b} (equal : a=b) (old : EarlierBanks D k a n)
    (s : Bool) (t : DescentResetLocalRoster.Root k (2^n)) :
    ((congrArg (fun c=>EarlierBanks D k c n) equal).mp old).roots s t=old.roots s t :=by
  subst b
  rfl

end Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
  (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
  (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
  (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
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
variable (fitsStencil : e≤laneBits (S.groupWidth k tail age+k) payload (S.localWalshBits p (S.groupWidth k tail age+k) f (quota S.rounds))-k) (fitsSigned : e≤previous) (fitsCut : previous≤S.groupWidth k tail age) (count : Bank)
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


/-- The physical root array appears literally as the named before-collector input.
The only transport in its original definition is the previous source capacity. -/
theorem named_root_bank (s : Bool) (t : DescentResetLocalRoster.Root k (2^n)) :
    (namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count).pages s t=
      (rc).privatePageBank book s t :=by
  have half : (a).c/2=cap := by change (2*cap)/2=cap; omega
  unfold namedOriginals CandidateFront.calendarOriginals
  exact CandidateFront.EarlierBanks.root_after_cap_cast (D:=venue.degree) (k:=k) (n:=n) half _ s t

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count

/-- The true word limit and ordered root/actor/peer placements discharge both
numerical gates of Window.capture_catalogue. -/
theorem named_peer_after_roots (scene : (v).front.SceneRoom early ((v).issuedScene base₀ older) w) :
    (rc).preparedEnd book≤(v).front.peers early ∧ (v).front.peers early<2^w :=by
  have bounds:=(v).front.peer_boundaries early ((v).issuedScene base₀ older) scene
  have actors : (v).middle.stop base₀≤early :=by
    change _≤(v).actor.directoryEnd ((v).middle.stop base₀)
    rw [(v).actor.translated]
    exact Nat.le_add_right ..
  rw [named_root_prepared_end (fitsStencil:=fitsStencil) (fitsSigned:=fitsSigned) (fitsCut:=fitsCut)]
  exact ⟨((actors.trans bounds.1).trans bounds.2.1).trans bounds.2.2.1,
    bounds.2.2.2.trans_lt scene.peers.total⟩

theorem fromNamed_root_bank (previousMeta previousArguments : ℕ) (initial : Bool)
    (prepared : (rc).PreparedFits book) (scene : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (s : Bool) (t : DescentResetLocalRoster.Root k (2^n)) :
    (DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
      previousMeta previousArguments initial prepared scene).earlier.pages s t=(rc).privatePageBank book s t :=
  named_root_bank G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count s t

/-- All actual private-root input pages are within the subsequent joint scan's
address bound. This is the pages field of the named date's Ready predicate. -/
theorem fromNamed_ready_pages (previousMeta previousArguments : ℕ) (initial : Bool)
    (prepared : (rc).PreparedFits book) (scene : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (s : Bool) (t : DescentResetLocalRoster.Root k (2^n)) :
    ((DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
      previousMeta previousArguments initial prepared scene).earlier.pages s t).Fits w ((v).jointEnd base₀) :=by
  rw [fromNamed_root_bank]
  have pre:=named_peer_after_roots G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count scene
  have seen:=((rc).privatePage_room book s t _ pre.1 pre.2).1
  have bounds:=(v).front.peer_boundaries early ((v).issuedScene base₀ older) scene
  exact ⟨seen.1,seen.2.1,seen.2.2.trans (bounds.2.2.2.trans (((v).peer_prefix base₀).trans ((v).receipt_order base₀).1))⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
