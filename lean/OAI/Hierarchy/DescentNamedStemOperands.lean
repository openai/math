import OAI.Hierarchy.DescentNamedSceneInputs

namespace OAI
/-! # Stem operand addresses from the original named evidence window -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
  (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
  (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
  (io : Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
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
local notation "early" => (v).actorEnd base₀
local notation "pop" => S.hostSize age
local notation "src" => atlasSender atlas sh start count io.hubs g (2^n) roots w
local notation "rfield" => ResetMiddle.fieldWidth venue.degree cap n k Ht
local notation "F₀" => (v).front
local notation "peers" => (F₀).peers early
local notation "stop" => (F₀).peer.endAddress peers

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "liveScene" => (v).issuedScene base₀ older

/-- The stem issuer and the evidence scan read the same operand for every signed query and lane. -/
theorem named_stem_operand_eq (q : Fin (v).front.signedQueries) (i : Fin ((v).front.peer.oldDegree+2)) :
    (liveScene).stems.operands q i=(liveScene).evidence.source q i := rfl

/-- The evidence source bounds established on the original root window certify the stem scan
at precisely the end of the actor directory. -/
theorem named_stem_operands :
    (∀q i,((liveScene).stems.operands q i).Fits w ((v).actorEnd base₀)) ↔
      (∀q i,((liveScene).evidence.source q i).Fits w ((v).actorEnd base₀)) := Iff.rfl

/-- The actual root window, host roster and prepared arena certify all native operands. -/
theorem named_stem_operands_fit (stencil : (P).Room w)
    (geometry : (src).OperandRoom pop (2^cc) (2^e) w ((rc).headerEnd book))
    (laid : (rc).preparedEnd book ≤ early) (small : 4 < 2^w)
    (hosts : pop < 2^w) (degrees : venue.degree+1 < 2^w)
    (packed : 2^e*max (rfield*8) (F₀).peer.bits ≤ w/2) (endRoom : stop < 2^w) :
    ∀q i,((liveScene).stems.operands q i).Fits w early :=
  (named_scene_inputs G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
    stencil geometry laid small hosts degrees packed endRoom).1

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
