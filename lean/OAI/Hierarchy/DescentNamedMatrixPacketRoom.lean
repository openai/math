import OAI.Hierarchy.DescentNamedResetRootPagesFit
import OAI.Hierarchy.DescentOperandPreparedPackets

namespace OAI
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

local notation "field" => (v).middle.rootField

include fitsStencil fitsSigned fitsCut count in
/-- Read the actual matrix shelf's input/output field count from the scheduled
root memory word. Its native lookup uses the same selected pitch as the shelf. -/
theorem fromNamed_matrix_packing
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e)
    (small : 8*(v).groupWidth≤payload) (word : payload≤w) (ceiling : (a).fullEnd floor<2^w)
    (capacity : venue.cap=cap) :
    (2^e)*max (field*DescentRotorWindowArchive.count venue.degree (2^k) venue.cap)
      (DescentRotorWindowArchive.output n (2^k) venue.cap)≤w/2 ∧
    DescentSignedCableCodec.width venue.degree venue.cap≤field ∧ Ht+2≤field :=by
  have all:= (chosen_root_pages_fit G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count chosen pitch
    small word ceiling).2 (DescentOperandRootPull.matrixPage k n)
  have half : (a).c/2=cap :=by change (2*cap)/2=cap;omega
  change (2^e)*max (field*DescentRotorWindowArchive.count venue.degree (2^k) ((a).c/2))
    (DescentRotorWindowArchive.output n (2^k) ((a).c/2))≤w/2 at all
  rw [half,←capacity] at all
  refine ⟨all,?_,?_⟩
  · rw [capacity]
    exact le_trans ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_left _ _)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
