import OAI.Hierarchy.DescentNamedResetPreflight
import OAI.Hierarchy.DescentNamedOperandComplete
import OAI.Hierarchy.DescentNamedOperandSetupRoom
import OAI.Hierarchy.DescentNamedResetControlsRoom
import OAI.Hierarchy.DescentNamedEnteredProgram

namespace OAI
/-! Native address bounds for the complete named reset, from the preceding physical venue. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup DescentWalshPrecision
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open DescentPlainTerminal.Suffix DescentSixParty.PackedFlow.Padded ProtocolRAM
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
local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count

local notation "front" => (v).front
local notation "bb" => S.localWalshBits p (cc+k) f (quota S.rounds)
local notation "prime₀" => (a).PrimeRoom start ((a).ingress.source floor) count (S.groupCount age) venue.degree w


local notation "early" => (v).actorEnd base₀
local notation "sp₀" => NamedEntrySpace G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w count

local notation "support" => NamedCodeRoom G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count

/-- The compiler can select its physical root book and actor code before reading memory. -/
theorem named_code_room (space : sp₀) : support := by
  obtain ⟨_,_,prepared,scene⟩:=named_entry_ready G S board k tail age p f g drift degree payload e previous
    M nextM C packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count space
  exact ⟨prepared,scene⟩

variable (previousMeta previousArguments : ℕ) (initial : Bool)
local notation "inputAt" res:arg => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
  previousMeta previousArguments initial (res).prepared (res).scene

/-- Every register, input expression and output region of this named program fits
on arbitrary initial RAM, using the two preceding native archive extents. -/
theorem DateInputs.named_ready (space : sp₀) (res : support) (hosts : venue.hosts=S.hostSize age)
    (within : age<S.length) (roles : (v).setup.retained.priorMetaLimit initial previousMeta≤floor)
    («arguments» : (v).setup.retained.priorOperandLimit previousArguments≤floor) :
    (inputAt res).Ready := by
  have lanes:0<M:=by rw [space.pitch]; exact Nat.two_pow_pos _
  have prime:=named_entry_ready G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count space
  have placed:=DateInputs.fromNamed_placed G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial res.prepared res.scene space.groups space.radix within lanes space.ceiling roles «arguments»
  have controls:=DateInputs.fromNamed_controls_room G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial res.prepared res.scene hosts space.groups space.radix within lanes space.ceiling
  obtain ⟨_,_,_,_,_,_,_,roof⟩:=(a).entered_bounds floor space.ceiling
  have operandFields:=DateInputs.named_operand_access G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial res.prepared res.scene roof placed
  exact DateInputs.named_ready_of_operands G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial res.prepared res.scene space prime.1 prime.2.1 controls placed operandFields

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
