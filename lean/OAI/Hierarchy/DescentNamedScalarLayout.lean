import OAI.Hierarchy.DescentOriginalScalarPrefix
import OAI.Hierarchy.DescentNamedResetDateInputs

namespace OAI
/-! # Fixed scalar instruction arguments of the original reset date -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
  (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
  (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
  (io : Dated.Operands) (floor w : ℕ)
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
variable (fitsStencil : e≤ wide-k) (fitsSigned : e≤ previous) (fitsCut : previous≤ cc) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀


local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
    (scene : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
local notation "u" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
  previousMeta previousArguments initial prepared scene
set_option maxHeartbeats 640000 in
theorem named_original_scalar_layout : (u).OriginalScalarLayout := by
  let choices := DescentResetLocalRoster.rootSlots k (2^n)*(2^n+2^Ht)
  let shapeCount := (DescentDenseHostOrder.roster board k Ht).card
  let ceiling := max choices (max (venue.degree+2) shapeCount)+1
  have short : ceiling ≤ 2^Nat.clog 2 ceiling := Nat.le_pow_clog (by decide) _
  have lower : max (venue.degree+2) shapeCount ≤ max choices (max (venue.degree+2) shapeCount) := Nat.le_max_right ..
  have deg := (Nat.le_max_left (venue.degree+2) shapeCount).trans lower
  have shapes := (Nat.le_max_right (venue.degree+2) shapeCount).trans lower
  refine ⟨rfl,fun _=>rfl,fun _=>rfl,fun _=>rfl,fun _=>rfl,fun _=>rfl,?_,?_,?_⟩
  · change venue.degree < 2^Nat.clog 2 (venue.degree+2)
    exact (by omega : venue.degree< venue.degree+2).trans_le (Nat.le_pow_clog (by decide) _)
  · change venue.degree < 2^Nat.clog 2 ceiling
    exact (by dsimp only [ceiling];omega : venue.degree < ceiling).trans_le short
  · have shapeRoom : shapeCount ≤ 2^Nat.clog 2 ceiling :=
      (by dsimp only [ceiling]; omega : shapeCount ≤ ceiling).trans short
    exact shapeRoom

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
