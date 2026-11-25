import OAI.Hierarchy.DescentPhysicalSheetRoom
import OAI.Hierarchy.DescentNamedResetDateInputs
import OAI.Hierarchy.DescentResetPeerCorrectionRoom

namespace OAI
/-! # Space for the named reset candidate and ranking phases -/
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

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count

variable (previousMeta previousArguments : ℕ) (initial : Bool)
local notation "I" pr:arg sc:arg => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial pr sc
local notation "start₁" => (v).sheetsStart base₀
local notation "A" => (v).receiver
local notation "q" pr:arg sc:arg => (I pr sc).sectors

theorem DateInputs.named_sheet_access (prepared : (rc).PreparedFits book)
  (scene : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (roof : (v).finalEnd base₀<2^w) :
    (∀x j,((q prepared scene).header x j).Fits w start₁) ∧ (∀x j,((q prepared scene).original x j).Fits w start₁) ∧
    (A).hosts*chunks (A).groups (A).lanes≤2^(q prepared scene).pageBits ∧
    DescentResetCandidatePair.endAddress start₁ (A).blocks
      (DescentResetFieldAssembler.CandidateSheet.size (q prepared scene).stems (q prepared scene).contacts (q prepared scene).privates) (q prepared scene).pageBits=(v).candidateEnd base₀ ∧
    (v).RankPortRoom base₀ w ∧ ((v).rankBook ((v).linkedRankInputs (q prepared scene) start₁) base₀).Previous w:=by
  have ⟨head,old,rows,matched⟩:=(I prepared scene).sheet_access rfl rfl rfl rfl rfl rfl rfl rfl rfl roof
  have pal : 0<(v).front.peer.shapes:=(by decide : 0<2).trans_le (two_le_roster_card board k Ht)
  exact ⟨head,old,rows,matched,(I prepared scene).rank_rooms_of_roof pal (Nat.le_refl _) matched rfl rfl rfl roof⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
