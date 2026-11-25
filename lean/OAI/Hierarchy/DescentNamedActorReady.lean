import OAI.Hierarchy.DescentNamedResetDateInputs
import OAI.Hierarchy.DescentPhysicalRootSpectra
import OAI.Hierarchy.DescentDatedActorGateRoom
import OAI.Hierarchy.DescentResetActorBookFits

namespace OAI
/-! The installed root stencil and its scalar depth and shared-book pages supply
every input to the named successor actor. -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentSIMDLookup ProtocolRAM
noncomputable section
variable {D cap N n r c H G K R M h l t field Ht w : ℕ}

/-- Read the projected shape operand at the first local block and first output side. -/
theorem stencil_fits_before (a : Receiver D cap N n r c H G K R M h l t field Ht w)
    (p : a.PrefixFits) : a.stencil.Fits w a.projectionEnd := by
  let x : Fin (2^r) := ⟨0,Nat.two_pow_pos _⟩
  let tag : Column (2^r) cap := .inl (0,x)
  let i := column (2^r) cap tag
  have before : a.atQuery i ≤ a.projectionEnd :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ i.isLt.le) _
  have source := (p.projected i).prior
  change (spec a.stencil a.tapped t D ((column (2^r) cap).symm ((column (2^r) cap) tag))).source.Fits w _ at source
  rw [Equiv.symm_apply_apply] at source
  change a.stencil.Fits w (a.atQuery i) at source
  exact ⟨source.1,source.2.1,source.2.2.trans before⟩

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentFallbackPeriod DescentSIMDLookup ProtocolRAM
noncomputable section
set_option quotPrecheck false

variable {a : PhysicalReset} (z : a.Atlas) (sh : a.StencilShape) (start : ℕ)
  (count hub : Bank) (g Y : ℕ) (roots : a.RootInputs) (w : ℕ)

local notation "v" => a.successor
local notation "s" => a.stencilPhase sh start count hub g Y
local notation "rc" => a.rootPhase sh start count hub g Y roots w
local notation "book" => atlasBook z sh start count hub g Y roots w
local notation "ab" => (v).middle.stop (a.rebased start)
local notation "source" h => atlasActors z sh start count hub g Y roots w h

theorem atlas_actor_ready (size : ActorFit z roots) (ready : (rc).PreparedFits book)
    (endEq : (rc).preparedEnd book=ab) (room : (s).Room w)
    (estimator : (a.estimator start).Fits w) (number : count.base+count.size≤ start)
    (sameHosts : (v).actor.hosts=(v).middle.signedHosts)
    (sameGroups : (v).actor.common=(v).middle.stencil.c)
    (sameLanes : (v).actor.lanes=(v).middle.signedLanes)
    (width : (v).actor.common≤w) (limit : (v).actorEnd (a.rebased start)<2^w) :
    (v).actor.Ready (source size) ab w := by
  have lim := (book).limits (rc).projectionEnd (v).middle.signedHosts
    (2^(v).middle.stencil.c) (v).middle.signedLanes
  have after : (rc).headerEnd book≤ab := by
    rw [←endEq]
    exact Nat.le_add_right ..
  have high : (rc).projectionEnd≤ab := (lim.1.trans (lim.2.1.trans lim.2.2)).trans after
  have before : (s).endAddress≤ab := (rc).origin_le_projection.trans high
  have raw := (a.root_spectra_fit sh start count hub g Y estimator ab before).1
  have num := (s).S.banks (s).X (s).base (s).bank room.operands
  obtain ⟨_,_,_,_,_,_,_,_,old⟩ := num
  have top : (s).S.afterHeader (s).base≤(s).endAddress := (s).S.header_before_output _
  have feed (b : Bank) {lo : ℕ} (available : b.Fits w lo) (away : lo≤(s).endAddress) :
      b.Fits w (s).endAddress := ⟨available.1,available.2.1,available.2.2.trans away⟩
  have refs := atlas_actor_refs z sh start count hub g Y roots w size ready endEq sameHosts
    (feed _ room.operands.old.roster (old.trans top)) (feed _ room.operands.old.hubs (old.trans top))
  have cut : ab<2^w :=
    ((v).actor.scalar_before _).trans_lt (by
      have bound : (v).actor.endAddress ab≤(v).actorEnd (a.rebased start) := Nat.le_add_right ..
      have output : ((v).actor.gate ab).output≤(v).actor.endAddress ab := Nat.le_add_right ..
      obtain ⟨a₁,a₂,a₃⟩ := (v).actor.gate_order ab
      have toRepeat : ((v).actor.gate ab).scalar ≤ ((v).actor.gate ab).repeatBase :=
        a₁ ▸ Nat.le_add_right ..
      have toGate : ((v).actor.gate ab).repeatBase ≤ ((v).actor.gate ab).gateBase := by
        rw [←a₂]
        exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
      have toOut : ((v).actor.gate ab).gateBase ≤ ((v).actor.gate ab).output :=
        a₃ ▸ Nat.le_add_right ..
      exact (toRepeat.trans (toGate.trans (toOut.trans (output.trans bound)))).trans_lt limit)
  have early : start≤ab := by
    have h := a.occupied start
    have mid := (v).middle.translated (a.rebased start)
    omega
  have pop : count.Fits w ab := ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt ((number.trans early).trans_lt cut),
    number.trans early⟩
  have limbs : 0<(v).actor.lanes := sameLanes.symm ▸ roots.lanes
  have parts := (v).actor.chunks_room limbs width
  have trueSource : (rc).stencil = ⟨(s).output,Nat.clog 2 ((v).actor.hosts*(v).actor.chunksPerHost)⟩ := by
    change (⟨(s).output,Nat.clog 2 ((v).middle.signedHosts*chunks (2^(v).middle.stencil.c) (v).middle.signedLanes)⟩ : Bank)=_
    simp only [ActorSetup.chunksPerHost,ActorSetup.groups,sameHosts,sameGroups,sameLanes]
  have srcFit := (rc).stencil_fits_before ready.toPrefixFits
  have st : (source size).stencil.Fits w ab := by
    change (⟨(s).output,Nat.clog 2 ((v).actor.hosts*(v).actor.chunksPerHost)⟩:Bank).Fits w ab ∧ True
    rw [←trueSource]
    exact ⟨⟨srcFit.1,srcFit.2.1,srcFit.2.2.trans high⟩,trivial⟩
  exact ⟨raw,refs,(v).actor.gate_geometry ab w count (source size).control (source size).stencil
    pop st parts.1 limit,parts.2,limit⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

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

local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count

theorem DateInputs.fromNamed_actor_ready (previousMeta previousArguments : ℕ) (initial : Bool)
    (prepared : (rc).PreparedFits book)
    (scene : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (prime : (a).PrimeRoom start ((a).ingress.source floor) count (S.groupCount age) venue.degree w)
    (stencil : (P).Room w) (endEq : (rc).preparedEnd book=actorBase)
    (commonWide : cc≤w) (space : early<2^w) :
    (v).actor.Ready (I₀ previousMeta previousArguments initial prepared scene).actor actorBase w :=
  atlas_actor_ready atlas sh start count io.hubs g (2^n) roots w ⟨rfl⟩ prepared endEq stencil
    prime.fit prime.countLow rfl rfl rfl commonWide space

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
