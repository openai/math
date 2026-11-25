import OAI.Hierarchy.DescentNamedOriginalVolume
import OAI.Hierarchy.DescentOriginalNumberStructural
import OAI.Hierarchy.DescentOriginalControlPrice

namespace OAI
/-! Uniform structural coefficient for the physically numbered parent rows. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
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
variable (fitsStencil : e≤(laneBits ((S.groupWidth k tail age)+k) payload (S.localWalshBits p ((S.groupWidth k tail age)+k) f (quota S.rounds)))-k) (fitsSigned : e≤previous) (fitsCut : previous≤(S.groupWidth k tail age)) (count : Bank)
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
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : ((((named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rootPhase (namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w)).PreparedFits (atlasBook (namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor (namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) count) (namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w))
    (scene : ((((named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).front.SceneRoom (((((named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).actorEnd (((named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor))) (((((named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).issuedScene (((named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor)) (namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count)) w)
local notation "u" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
  previousMeta previousArguments initial prepared scene
local notation "ss" => (v).sheets
local notation "r" => ((v).remap base₀).endAddress
local notation "deck" => (ss).inputDonorsEnd r
local notation "N₀" => 2^k*(2*cap)


open DescentStaticWordColumn

local notation "U₀" => (256+28*((v).front.signedQueries/2))
local notation "V₀" => (v).contactShape.originalWork


open DescentResetMixedWordRAM DescentDenseHostOrder CandidateFront
local notation "H" => S.hostSize age
local notation "G₀" => S.groupCount age
local notation "area" => ResetOutput.receiptArea payload H (chunks G₀ M)
local notation "shapeCount" => (DescentDenseHostOrder.roster board k Ht).card
local notation "growth" => 2^S.hostGain*S.radix
local notation "factor" => (3*shapeCount+2*growth+1)


local notation "Y₀" => (2^n : ℕ)
local notation "Z₀" => (2^Ht : ℕ)
local notation "P₀" => DescentResetCableSlots.cableCap board Ht
local notation "A₀" => (2*((Y₀+1)+((2*d+4)*Y₀+(Y₀+1)*2^(Ht+1))))
local notation "B₀" => OriginalControlPrice.controlBound venue.degree Y₀ Z₀ P₀ (2^k) cap
local notation "Q₀" => OriginalControlPrice.factorBound venue.degree Y₀ Z₀ P₀ A₀ (2^k) cap growth

theorem named_number_factor :
    (u).numbered.numberFactor U₀ V₀ 64*factor ≤ Q₀ := by
  let X:=2^k
  let t:=X*(2*cap)
  let rootCount:=X*2+(X*2)*(Y₀+1)
  have rootSize : DescentResetLocalRoster.rootSlots k Y₀=rootCount :=by
    simp only [DescentResetLocalRoster.rootSlots,pow_succ];rfl
  have control : B₀=3*(X*X)+t+X+2*(rootCount*(Y₀+Z₀))+2*t+2*(rootCount*P₀)+t+
      (256+28*(2*t))+(56+(12+8*(1+(venue.degree+1)*55))) :=rfl
  have shapes : shapeCount≤A₀*(2^k*2) :=by
    simpa only [pow_succ] using DescentDenseHostOrder.roster_bound board k Ht
  have size := (u).numbered.numberFactor_polynomial U₀ V₀ B₀
    (by change 3*(X*X)≤_;rw [control];omega)
    (by change t≤_;rw [control];omega)
    (by change X≤_;rw [control];omega)
    (by change 2*(DescentResetLocalRoster.rootSlots k Y₀*(Y₀+Z₀))≤_;rw [rootSize,control];omega)
    (by change 2*t≤_;rw [control];omega)
    (by change 2*(DescentResetLocalRoster.rootSlots k Y₀*P₀)≤_;rw [rootSize,control];omega)
    (by change t≤_;rw [control];omega)
    (by change 256+28*((2*t)/2)≤_;rw [control];have:=Nat.div_le_self (2*t) 2;omega)
    (by change max 56 (12+8*(1+(venue.degree+1)*55))≤_;rw [control];omega)
  exact Nat.mul_le_mul size (by omega)

theorem original_priced (pitch : M=2^e) (reached : age<S.length)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (key : (cc+k+1)^2≤payload/2) (ceiling : (a).fullEnd floor<2^w)
    (markers : ((v).front.donor.markers ((v).front.donorStart early)
      (v).contactShape.shapes (v).contactShape.markerBits).endAddress≤(v).trunkEnd base₀)
    (keys : ∀t,t∈(v).receiverUnits→t*(v).receiver.lanes≤payload/2) :
    ((u).numbered.time r+7*names ((u).numbered.code r w))≤Q₀*area :=
  (original_volume G S board k tail age p f g drift degree payload e previous M nextM C packet oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
    prepared scene pitch reached baseGroups radix key ceiling markers keys).trans (Nat.mul_le_mul_right _
      (named_number_factor G S board k tail age p f g drift degree payload e previous M nextM C packet
        oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
        previousMeta previousArguments initial prepared scene))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
