import OAI.Hierarchy.DescentNamedPublicSocketConfig
import OAI.Hierarchy.DescentRelayOperandRelabel
import OAI.Hierarchy.DescentRelaySocketObserved
import OAI.Hierarchy.DescentCalendarRealStemAux
import OAI.Hierarchy.DescentIssuedPublicTreeFields
import OAI.Hierarchy.DescentNamedTreeWordRoom
import OAI.Hierarchy.DescentResetPeerJointAuxValues

namespace OAI
/-! # The two original donor coordinates and the old self correction on a named row -/
namespace Hierarchy.DescentStemCoordinateBook.Shape
open DescentColonies
noncomputable section
theorem value_relabel {b c a H G M b₁ c₁ a₁ H₁ G₁ M₁ field field₁ : ℕ}
    (dim:b=b₁) (fine:c=c₁) (res:a=a₁) (groups:G=G₁)
    (μ:DescentGL.Layout b) (ν:DescentGL.Layout b₁) (basis:HEq μ ν)
    (axis:Fin 3) (x:Block c) (x₁:Block c₁) (xx:x.val=x₁.val)
    (lo:Block a) (lo₁:Block a₁) (ll:lo.val=lo₁.val) (g:Fin G) (g₁:Fin G₁) (gg:g.val=g₁.val) :
    (⟨b,c,a,H,G,M,field⟩:Shape).value μ axis x lo g=
      (⟨b₁,c₁,a₁,H₁,G₁,M₁,field₁⟩:Shape).value ν axis x₁ lo₁ g₁ :=by
  subst b₁;subst c₁;subst a₁;subst G₁
  cases eq_of_heq basis
  cases Fin.ext xx
  cases Fin.ext ll
  cases Fin.ext gg
  rfl
end
end Hierarchy.DescentStemCoordinateBook.Shape


namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F X : Type} [Field F] {d : ℕ} {abits : X→ℕ} {W : MarkedWorld F d X abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤(laneBits ((S.groupWidth k tail age)+k) payload (S.localWalshBits p ((S.groupWidth k tail age)+k) f (quota S.rounds)))-k) (fitsSigned : e≤previous) (fitsCut : previous≤(S.groupWidth k tail age)) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : ((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rootPhase (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w)).PreparedFits (atlasBook (namedAtlas G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) count) (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w))
  (sceneRoom : ((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).front.SceneRoom (((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).actorEnd (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor))) (((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).issuedScene (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor)) (namedOriginals G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count)) w)
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage

local notation "res" => (Z).k-(T).commonDepth
local notation "U" => (v).actor

open DescentSortedRoster

open CandidateFront ClosedReset.Window DescentSortedRoster DescentResetLocalRoster DescentResetCandidatePair
open DescentFallbackPeriod.Projected DescentResetRankedWindows DescentResetOriginalSlots DescentContactDonorFront
open DescentPackedPrivateMenu DescentResetGates DescentGL
open ClosedReset.Window DescentResetControlRegisters DescentVenueQuantityPlanes
local notation "height₁" => S.hostSize (age+1)
local notation "group₁" => S.groupCount (age+1)
local notation "control" => (v).controlRegisters
local notation "first_" => (v).controlFloor base₀
local notation "prior_" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue

local notation "C₀" => (v).setup
local notation "stage_" x:arg => (control).live first_ (x:DescentColonies.Block k).val
local notation "regs_" x:arg => (control).ports first_ ((a).c/2) (x:DescentColonies.Block k).val ((U).directory actorBase).inverse
  ((U).depths actorBase) ((U).levels actorBase)
local notation "deck_" x:arg => OperandMenu.publicPorts («a»:=a) sh start count io.hubs g (2^n) (stage_ x) (regs_ x)
local notation "head_" => (C₀).placement.newHosts
local notation "gang_" => (C₀).placement.groups
local notation "rows_" x:arg => (b₀:Bool)→Fin ((deck_ x).packets.stage 0 b₀).fields→Fin (deck_ x).packets.blocks→
  Fin head_→Fin gang_→Cell ((deck_ x).casts.width 0)

open DescentPaidResidentCount.Reset DescentResetPublicOperandBook
local notation "rotor" => (v).setup.rotorBits
local notation "q₁" => (v).setup.queryBits
local notation "stages₁" => ResetInput.calendarLanes S G.b (age+1)
local notation "pcfg" => publicOperandConfig B rotor q₁ M stages₁ ((Z).unit/p) S.retainedNodes
  (S.retainedArgumentsAt G drift) p
local notation "config" => publicOperands (u).atlas (u).roots (u).menu.payload
local notation "cfgEq" dd:arg cd:arg gr:arg => (DateInputs.fromNamed_public_socket_config (B:=B) accepted drift degree payload e
  previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
  previousArguments initial prepared sceneRoom dd cd gr).2
local notation "extent₀" => S.groupWidth k tail age+k
local notation "donors" => 2^(extent₀-(T).commonDepth)

local notation "co" => (v).sheets.stemSources.coord
local notation "rgeom" => extent₀-(T).commonDepth
local notation "adjusted₁" => ({ (flatConfig B rotor q₁ M stages₁ ((Z).unit/p) S.retainedNodes (S.retainedArgumentsAt G drift)) with
    oldDegree := input.placement.degree
    oldCap := input.placement.cap
    «donors» := donors
    fineBits := k
    fieldBits := rotor
    residual := res
    maxDepth := GroupStage.depthBound D n f g } : DescentFallbackOperandBranch.Config)
local notation "rawAt" xx:arg hh:arg gg:arg menu:arg cut₀:arg => (u).menu.publicData sh start count io.hubs g (2^n)
  (stage_ xx) (regs_ xx) menu cut₀ (xx:DescentColonies.Block k).val hh gg

set_option maxHeartbeats 640000 in
theorem DateInputs.fromNamed_descent_tree_values
    (dd:venue.degree=D) (cd:input.placement.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256) (gr:z=S.grainAt G.b p (age+1))
    (positive:0<cap) (R:(u).MeasuredChannels (Fintype.card B.next.V)) (dst:Memory w)
    (room:DateInputs.CaptureRoom R dst) (selfAt:CapturedSelf B (u) R) (x:DescentColonies.Block k)
    (menu:(deck_ x).Values head_ gang_) (paid:(deck_ x).casts.bits=(C₀).fallbackBits)
    (packets:rows_ x)
    (issued:menu=(u).issuedPublicValues x R B.frame.basis rfl rfl rfl rfl rfl rfl menu.active menu.register packets)
    (h₁:Fin height₁) (g₁:Fin group₁) :
    let row:=Config.relabel (cfgEq dd cd gr) B.dimension.symm (rawAt x h₁ g₁ menu paid)
    let num:=relayPhysicalRow (field:=rotor) (query:=q₁) (lanes:=M) (batches:=stages₁) (split:=(Z).unit/p)
      (nodes:=S.retainedNodes) (args:=S.retainedArgumentsAt G drift) (grain:=p) B row
    ((adjusted₁).header num 3).val=stemSelfDigit B (originalTrunkRack B) h₁ ∧
    ∀(j:Fin (donors*(2*input.placement.cap))) (axis:Fin 2),
      ((adjusted₁).digit num j (axis.castLE (by decide))).val=
        (coords B height₁ M rotor).value B.frame.basis axis.castSucc x
          (finProdFinEquiv.symm j : Fin donors×Fin (2*input.placement.cap)).1 g₁ :=by
  intro row num
  have cuts:=ResetOutput.fromBoard_tree_caps G S board k tail age p f g drift degree payload e previous M nextM
    C packet prior_ base₀ positive
  have narrowed:=Config.relay_relabel (cfgEq dd cd gr) B.dimension.symm
    (relay_socket_config (field:=rotor) (query:=q₁) (lanes:=M) (batches:=stages₁)
      (split:=(Z).unit/p) (nodes:=S.retainedNodes) (args:=S.retainedArgumentsAt G drift) B) (rawAt x h₁ g₁ menu paid)
  have selfSmall : DescentResetPeerJointPacked.Aux.value (v).front.peer.shapes R.names R.prior R.near h₁ 3<
      2^(v).sheets.metaBits :=
    DescentResetPeerJointPacked.Aux.value_lt _ _ _ _ _ 3 room.distinct room.shapes room.keys room.previousSelf
  constructor
  · have headerRead := narrowed.1 3
    have sourceRead := (u).public_tree_host x R B.frame.basis rfl rfl rfl rfl rfl rfl packets
      menu paid issued h₁ g₁ selfSmall (selfSmall.trans_le (Nat.pow_le_pow_right (by decide) cuts.2.2))
    have selfRead := selfAt B.next.valid.host h₁
    apply Eq.trans headerRead
    exact sourceRead.trans selfRead
  · intro j axis
    let lo:=(finProdFinEquiv.symm j : Fin donors×Fin (2*input.placement.cap)).1
    have resdim : rgeom=k :=by rw [B.commonDepth];omega
    have half : (2*cap)/2=cap :=by omega
    have cap₀ : (config).oldCap=input.placement.cap :=half.trans cd.symm
    have total : (config).oldConfig.count=donors*(2*input.placement.cap) :=by
      change 2^k*(2*(config).oldCap)=_;rw [cap₀,resdim]
    let ix:=j.cast total.symm
    let d₀:=(finProdFinEquiv.symm ix : Fin (config).donors×Fin (2*(config).oldCap)).1
    have address : d₀.val=lo.val :=by
      change j.val/(2*(config).oldCap)=j.val/(2*input.placement.cap)
      rw [cap₀]
    have limit : d₀.val<2^(co).residual :=by
      change d₀.val<2^k
      exact (address.trans_lt lo.isLt).trans_le (le_of_eq (congrArg (2^·) resdim))
    have digit:=((co).donor_bound B.frame.basis axis x ⟨_,limit⟩ g₁)
    have bounded : (co).value B.frame.basis axis.castSucc x ⟨d₀.val,limit⟩ g₁≤2^k :=by
      simpa only [show (co).residual=k from rfl,show (co).fine=k from rfl,max_self] using digit
    have value₀:=(u).public_tree_donor x R B.frame.basis rfl rfl rfl rfl rfl rfl packets menu paid issued
      h₁ g₁ ix axis x.isLt limit (bounded.trans_lt cuts.1) (bounded.trans_lt cuts.2.1)
    have digitRead := narrowed.2.1 j ix rfl (axis.castLE (by decide))
    apply Eq.trans digitRead
    apply Eq.trans value₀
    exact DescentStemCoordinateBook.Shape.value_relabel rfl rfl resdim.symm rfl B.frame.basis B.frame.basis HEq.rfl
        _ _ _ rfl _ _ address _ _ rfl

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
