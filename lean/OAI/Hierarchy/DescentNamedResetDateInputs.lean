import OAI.Hierarchy.DescentNamedResetAtlas
import OAI.Hierarchy.DescentFrontEarlierRoot
import OAI.Hierarchy.DescentPhysicalNamedSectorDirectory
import OAI.Hierarchy.DescentPhysicalNamedOriginals

namespace OAI
/-! The full physical reset description obtained from the previous numeric venue. -/
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
variable (fitsStencil : e ≤ laneBits (S.groupWidth k tail age + k) payload
    (S.localWalshBits p (S.groupWidth k tail age + k) f (quota S.rounds)) - k)
  (fitsSigned : e ≤ previous) (fitsCut : previous ≤ S.groupWidth k tail age) (count : Bank)
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

/-- Static selectors for the previous seven-field pages and the two root dictionaries. -/
def namedOperandMenu (previousMeta previousArguments : ℕ) (initial : Bool) : OperandMenu atlas roots :=by
  have half : (a).c/2=cap:=by change (2*cap)/2=cap;omega
  refine ⟨previousMeta,previousArguments,p,initial,?_,rfl,rfl,?_,?_⟩
  · rw [half]
    rfl
  · let cutBits:=S.retainedExponent G k tail drift degree p age payload
    have small : cutBits≤cc:=Nat.min_le_left ..
    change 2^((cc-cutBits)+(cutBits+k)-cc)=2^k
    congr 1
    omega
  · exact half.symm

/-- The earlier operands are obtained from the same projected root banks, order table,
old host indices and compact actor directory as the receiver program. -/
def namedOriginals : (v).OriginalOperands base₀ :=by
  let code : DescentResetHostSize.Code k:=⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le _) (by decide)⟩
  let page : DescentSixParty.Chronology.RootPage k (2^n):=(false,.inr (code,none))
  let src:=(rc).atlasSources E (P).S (P).X (P).base (P).bank g (atlas).directions (atlas).hostIndex (.lit ((a).c/2))
    (a).depthCut (a).classBound (a).fullBudget (P).S.total (a).ports (atlas).board (atlas).packet
    (atlas).C (atlas).groupDigits (atlas).batches (atlas).layerBits (atlas).factor (atlas).primitive page
  let raw:=CandidateFront.EarlierBanks.fromRoot rc book src (atlas).hostIndex io.hubs
    ((v).actor.directory actorBase) ((v).actor.scene actorBase)
  have half : (a).c/2=cap:=by change (2*cap)/2=cap;omega
  have registered : CandidateFront.EarlierBanks venue.degree k cap n:=
    (congrArg (fun t=>CandidateFront.EarlierBanks venue.degree k t n) half).mp raw
  exact CandidateFront.calendarOriginals S board k tail age venue.degree f g (2^e) M
    (ResetMiddle.fieldWidth venue.degree cap n k Ht) ((v).front.metaBits) C packet cal early registered

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "menu₀" => namedOperandMenu G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil fitsSigned fitsCut count

/-- All safety arguments here are propositions over public addresses. The rank directory is the compact four-neighbor rack
produced before the first candidate scan. -/
def DateInputs.fromNamed (previousMeta previousArguments : ℕ) (initial : Bool)
    (prepared : (rc).PreparedFits book)
    (scene : (v).front.SceneRoom early ((v).issuedScene base₀ older) w) :
    (a).DateInputs start w where
  shape:=sh
  count:=count
  hub:=io.hubs
  src:=(a).ingress.source floor
  g:=g
  Y:=2^n
  sourceRows:=S.groupCount age
  oldDegree:=venue.degree
  «roots»:=roots
  «atlas»:=atlas
  bookFits:=prepared
  actorFit:=⟨rfl⟩
  earlier:=older
  sceneFits:=scene
  number:=namedNumber G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor older
  directory:=namedSectorDirectory G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor
  operandBlocks:=rfl
  operandChannels:=rfl
  menu:=menu₀ previousMeta previousArguments initial
  degree:=3

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
