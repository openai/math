import OAI.Hierarchy.DescentPhysicalOperandSetupRoom
import OAI.Hierarchy.DescentNamedResetDateInputs
import OAI.Hierarchy.DescentPhysicalOperandCuts
import OAI.Hierarchy.DescentDatedOperandPacketRows
import OAI.Hierarchy.DescentNamedResetRootPagesFit
import OAI.Hierarchy.DescentResetControlCuts

namespace OAI
/-! # Original reset bounds for the named, physically mounted operand menu -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open DescentOperandRootPull DescentFallbackPeriod.Projected DescentDyadicSpan ProtocolRAM
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

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "menu₀" => namedOperandMenu G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil fitsSigned fitsCut count

local notation "U" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count

/-- The two upper cutoffs of the genuine previous checkpoint suffice for issuing
the complete registered field directory at this reset. All other bounds come from
the current named layout and its actual prepared atlas. -/
theorem DateInputs.fromNamed_placed (previousMeta previousArguments : ℕ) (initial : Bool)
    (prepared : (rc).PreparedFits book) (scene : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k) (within : age<S.length)
    (positive : 0<M) (space : (a).fullEnd floor<2^w)
    (roles : (v).setup.retained.priorMetaLimit initial previousMeta≤floor)
    (args : (v).setup.retained.priorOperandLimit previousArguments≤floor) :
    (v).setup.Ready (U previousMeta previousArguments initial prepared scene).bank w ((v).operandFloor base₀) :=by
  let m:=menu₀ previousMeta previousArguments initial
  have saved:=named_root_prepared_end G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
  have cuts:=(v).cuts base₀
  have cb:=(v).control_address_bounds base₀
  have fromActor : early≤(v).operandFloor base₀:=cb.1.trans cb.2.2.1
  have inFloor : floor≤ start:=by
    change floor≤(a).ingress.endAddress floor
    rw [(a).ingress.translate floor]
    exact Nat.le_add_right ..
  have reserve:=(a).occupied start
  have old : floor≤(v).operandFloor base₀:=
    (((inFloor.trans (reserve.1.trans reserve.2.1)).trans cuts.middle).trans cuts.actors).trans fromActor
  have shape : (a).RootShape:=by
    have half : (a).c/2=cap:=by change (2*cap)/2=cap;omega
    refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
    · change 2*cap=2*((a).c/2);rw [half]
    · change DescentSignedCableCodec.width venue.degree cap=DescentSignedCableCodec.width venue.degree ((a).c/2)
      rw [half]
  have pair:=(named_packet_pair G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io.wire io.roster floor sh count io.hubs g (2^n) roots w book
    shape rfl rfl (by
      unfold atlasBook
      rw [ResetMiddle.issued_law_width]
      have dim : (E).dim = cc+k := by
        change (cc+k-wide)+wide=cc+k
        exact Nat.sub_add_cancel (Nat.min_le_left _ _)
      rw [dim]
      change (v).middle.rootLawWidth=ResetMiddle.lawWidth venue.degree ((a).c/2) n k (S.hostSize age)
        (2^cc) (2^e) (v).middle.rootField (v).middle.stencil.n (v).middle.stencil.levels (v).middle.stencil.total
      rw [show (a).c/2=cap by change (2*cap)/2=cap;omega]; rfl))
  have split : S.groupCount (age+1)*2^k=2^cc:=by rw [S.group_cut within,pow_add,S.group_power baseGroups radix]
  have front:=(v).operands_after_front base₀
  apply m.setup_ready sh start count io.hubs g (2^n) w prepared _ fromActor
    ((cb.2.2.2.trans cuts.metadata).trans_lt space) (roles.trans old) (args.trans old)
    _ _ _ _ _ pair split front.1 positive (Nat.two_pow_pos _) positive (Nat.two_pow_pos _)
  rw [saved]
  exact cuts.actors.trans fromActor

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
