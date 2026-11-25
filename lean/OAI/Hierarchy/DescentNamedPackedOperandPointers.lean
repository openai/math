import OAI.Hierarchy.DescentPhysicalResetDate
import OAI.Hierarchy.DescentNamedOperandSetupRoom
import OAI.Hierarchy.DescentPreparedOperandPairRead

namespace OAI
/-! # Saved matrix and fallback inputs of the two actual named packet gathers -/
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

local notation "O" => (v).setup.packets
local notation "firstCode" =>
  (⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le _) (by decide)⟩ :
    DescentResetHostSize.Code (v).middle.rootDepth)

/-- Real native lookup operands at the original paid roots, before the dated actor directory. -/
theorem DateInputs.named_packet_registers (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
    (scene : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (run : (U previousMeta previousArguments initial prepared scene).FinalInputs) (baseGroups : S.baseGroups=2^tail)
    (radix : S.radix=2^k) (within : age<S.length) :
    (O).original true=(U previousMeta previousArguments initial prepared scene).bank.window ∧
    (O).original false=run.ports.bank false (firstCode,none) ∧
    ∀side,((O).original side).Fits w ((rc).preparedEnd book) := by
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
  let ptr:=((v).front.parent early).base
  let pp:=preparedPair (rc) (book) ptr (v).sheets.hosts (v).sheets.groups (v).sheets.blocks M
  have same : (O)=pp:=pair
  have split' : pp.groups*pp.blocks=2^cc:=split
  have lookup (f₁ : Bool) : pp.original f₁=(rc).gatheredOperand (book) (pp.page f₁) :=by
    simp only [Pair.original,Pair.packed,split']
    rfl
  rw [same]
  refine ⟨(lookup true).trans ?_,(lookup false).trans ?_,?_⟩
  · rfl
  · rfl
  · intro side
    rw [lookup]
    exact (rc).gathered_fits (book) prepared (pp.page side)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
