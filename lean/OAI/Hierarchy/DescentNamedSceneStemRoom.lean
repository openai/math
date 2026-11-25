import OAI.Hierarchy.DescentNamedStemOperands
import OAI.Hierarchy.DescentSceneStemPortFits
import OAI.Hierarchy.DescentResetPublicCuts

namespace OAI
/-! The stem producer fits in the address range reserved by the named reset. -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open ProtocolRAM

/-- The donor and peer programs finish before the parent directory begins. -/
theorem actor_before_parent (v : CandidateFront) (base : ℕ) (same : v.oldLanes=v.peer.evidenceLanes) :
    base ≤ v.parentStart base := by
  have first : base ≤ v.oldKeys base := by
    dsimp [oldKeys,DescentResetStemKey.Columns.stop,DescentResetStemKey.Columns.start]
    omega
  have raw : v.oldKeys base ≤ v.rawTablesEnd base := by
    rw [←v.tables_end base same,(v.rawTables base).end_eq]
    exact Nat.le_add_right ..
  obtain ⟨d₁,d₂,d₃⟩:=v.donor.ordered (v.donorStart base)
  obtain ⟨p₁,p₂,p₃,p₄⟩:=v.peer.ordered (v.peers base)
  obtain ⟨a₁,a₂,a₃,a₄,a₅⟩:=(v.contactLayout base).ordered
  have donor : v.rawTablesEnd base ≤ v.donorEnd base:=d₁.trans (d₂.trans d₃)
  have contacts : v.donorEnd base ≤ v.peers base:=a₁.trans (a₂.trans (a₃.trans (a₄.trans a₅)))
  have peers : v.peers base ≤ v.peer.endAddress (v.peers base):=p₁.trans (p₂.trans (p₃.trans p₄))
  exact first.trans (raw.trans (donor.trans (contacts.trans (peers.trans (Nat.le_add_right ..)))))

namespace EarlierBanks
theorem hub_after_cap_cast {D k n a b : ℕ} (eq : a=b) (old : EarlierBanks D k a n) :
    ((congrArg (fun c=>EarlierBanks D k c n) eq).mp old).oldHub=old.oldHub := by
  subst b
  rfl
end EarlierBanks
end Hierarchy.DescentDatedAddressBook.CandidateFront

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
variable (fitsStencil : e≤laneBits (S.groupWidth k tail age+k) payload (S.localWalshBits p (S.groupWidth k tail age+k) f (quota S.rounds))-k) (fitsSigned : e≤previous) (fitsCut : previous ≤ S.groupWidth k tail age) (count : Bank)
local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "liveScene" => (v).issuedScene base₀ older

local notation "front" => (v).front
local notation "early" => (v).actorEnd base₀
local notation "ds" => (v).actor.directory ((v).middle.stop base₀)

theorem named_stem_room (positive : 0<M)
    (before : ∀q i,((liveScene).evidence.source q i).Fits w early)
    (hubs : io.hubs.Fits w floor) (lower : floor ≤ early)
    (space : (v).trunkEnd base₀ < 2^w) :
    (front).parentStart early < 2^w ∧ (front).parentEnd early < 2^w ∧
      (front).StemRoom (liveScene).stems early w := by
  have actor := (front).actor_before_parent early rfl
  obtain ⟨parent,projected,_⟩ := (front).front_order early
  have trunk : (front).mixed early ≤ (v).trunkEnd base₀ :=
    (DescentResetTrunkCompactProgram.grow ..).trans (Nat.le_add_right ..)
  have last := trunk.trans_lt space
  have word := projected.trans_lt last
  have atParent := parent.trans_lt word
  have old := actor.trans parent
  obtain ⟨_,flags,_,counted,inverted⟩ := (ds).fits (actor.trans_lt atParent)
  have scratch : (ds).scratch ≤ early := by
    change (ds).first+3*(ds).pitch+1 ≤ (ds).first+(4*(ds).pitch+1+4*(ds).sites)
    omega
  have limit : (front).peer.hosts ≤ (ds).flags.size := (ds).ordered.1
  have origin : (older).oldHub=io.hubs := by
    have half : (a).c/2=cap := by change (2*cap)/2=cap; omega
    unfold namedOriginals CandidateFront.calendarOriginals
    exact CandidateFront.EarlierBanks.hub_after_cap_cast (D:=venue.degree) (k:=k) (n:=n) half _
  have hub : (older).oldHub.Fits w ((front).parentEnd early) := by
    rw [origin]
    exact ⟨hubs.1,hubs.2.1,hubs.2.2.trans (lower.trans old)⟩
  refine ⟨atParent,word,⟨?_,limit,positive,Nat.two_pow_pos _,?_,?_,last⟩⟩
  · exact ⟨flags.1,flags.2.1,flags.2.2.trans (scratch.trans actor)⟩
  · intro q i
    exact ProtocolRAMGeneratedWrite.fits_mono _ old (before q i)
  · exact (front).masked_ports_fit early older (ds).flags (ds).count (ds).inverse word
      ⟨counted.1,counted.2.1,counted.2.2.trans old⟩
      ⟨inverted.1,inverted.2.1,inverted.2.2.trans old⟩ hub

local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "src" => atlasSender atlas sh start count io.hubs g (2^n) roots w

/-- Every program in the named reset front fits the dated machine word. -/
theorem named_scene_ready (positive : 0<M)
    (stencil : (P).Room w)
    (geometry : (src).OperandRoom (S.hostSize age) (2^cc) (2^e) w ((rc).headerEnd book))
    (laid : (rc).preparedEnd book ≤ early) (small : 4 < 2^w)
    (hosts : S.hostSize age < 2^w) (degrees : venue.degree+1 < 2^w)
    (packed : 2^e*max ((ResetMiddle.fieldWidth venue.degree cap n k Ht)*8) (front).peer.bits ≤ w/2)
    (hubs : io.hubs.Fits w floor) (ceiling : (a).fullEnd floor < 2^w) :
    (front).SceneRoom early liveScene w := by
  have cuts := (a).entered_bounds floor ceiling
  have lower := cuts.1
  have space := cuts.2.2.1
  apply named_scene_room G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
    stencil geometry laid small hosts degrees packed
  · have paid : (front).mixed early ≤ (v).trunkEnd base₀ :=
      (DescentResetTrunkCompactProgram.grow ..).trans (Nat.le_add_right ..)
    exact paid.trans_lt space
  · intro before
    exact (named_stem_room G S board k tail age p f g drift degree payload e previous M nextM C packet
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
      positive before hubs lower space).2.2

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
