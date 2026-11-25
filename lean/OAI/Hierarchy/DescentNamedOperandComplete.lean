import OAI.Hierarchy.DescentNamedOperandAccess
import OAI.Hierarchy.DescentNamedResetRootPagesFit

namespace OAI
/-! Address bounds for every literal operand query and pointer field of a named reset. -/
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
local notation "R" pr:arg sc:arg => (v).linkedRankInputs (q pr sc) start₁


private theorem named_operand_slots :
    (v).front.signedQueries/2+(v).setup.strip≤(v).receiver.candidates := by
  let ex := S.retainedExponent G k tail drift degree p age payload
  have low : ex≤cc := Nat.min_le_left ..
  have donors : (v).setup.retained.donors=2^k := by
    change 2^(cc-ex+(ex+k)-cc)=2^k
    congr 1
    omega
  have aperture : (v).setup.strip=2^k*(2*cap) := congrArg (·*(2*cap)) donors
  rw [aperture]
  change 2*(2^k*(2*cap))/2+(2^k*(2*cap)) ≤ 2*(2^k*(2*cap))+(1+_)
  omega

theorem DateInputs.named_raw_operand_access (prepared : (rc).PreparedFits book)
  (scene : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (roof : (v).finalEnd base₀<2^w)
    (placed : (v).setup.Ready (I prepared scene).bank w ((v).operandFloor base₀)) :
    (∀i,((I prepared scene).rawOperands.query i).Fits w ((v).keepBase base₀)) ∧
    (∀i,((I prepared scene).rawOperands.kept i).Fits w ((v).keepBase base₀)):=by
  apply (I prepared scene).raw_operand_access roof placed
  · exact named_root_prepared_end G S board k tail age p f g drift degree payload e previous M
      nextM C packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
  · rfl
  · exact named_operand_slots G S board k tail age p f g drift degree payload e previous M
      nextM C packet oldLanes primitiveLanes printedBits venue io floor


theorem DateInputs.named_operand_access (prepared : (rc).PreparedFits book)
  (scene : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (roof : (v).finalEnd base₀<2^w)
    (placed : (v).setup.Ready (I prepared scene).bank w ((v).operandFloor base₀)) :
    (v).OperandEarly (I prepared scene).operand ((v).renderFromRanks (R prepared scene) base₀) w base₀:=by
  have rest:=DateInputs.named_sheet_access G S board k tail age p f g drift degree payload e previous M
    nextM C packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
    previousMeta previousArguments initial prepared scene roof
  apply (I prepared scene).operand_access roof rest.2.2.2.2.2 placed
  · exact named_root_prepared_end G S board k tail age p f g drift degree payload e previous M
      nextM C packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
  · rfl
  · exact named_operand_slots G S board k tail age p f g drift degree payload e previous M
      nextM C packet oldLanes primitiveLanes printedBits venue io floor

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
