import OAI.Hierarchy.DescentNamedTreeValues
import OAI.Hierarchy.DescentGoodNativeRow
import OAI.Hierarchy.DescentStemCoordinateObserved
import OAI.Hierarchy.DescentBankSavedPacket

namespace OAI
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
local notation "config" => publicOperands (u).atlas (u).roots (u).menu.payload
local notation "extent₀" => S.groupWidth k tail age+k

local notation "co" => (v).sheets.stemSources.coord
local notation "rgeom" => extent₀-(T).commonDepth
local notation "rawAt" xx:arg hh:arg gg:arg menu:arg cut₀:arg => (u).menu.publicData sh start count io.hubs g (2^n)
  (stage_ xx) (regs_ xx) menu cut₀ (xx:DescentColonies.Block k).val hh gg

local notation "unit" => (Z).unit/p
local notation "K" => publicOperandConfig B rotor q₁ M unit unit S.retainedNodes (S.retainedArgumentsAt G drift) p
local notation "born" s:arg root:arg cell:arg => (⟨(s,.inl root),DescentCommonPalette.rotorSiteEquiv (Z).graph d
  (DescentChosenRouter.selectedRotorLayers (Z).placement (Z).graph (Z).positive (Z).pay (Z).circuit s root)
  C (Z).width (Z).unit cell⟩ : (Z).bank.Site)
local notation "bankSite" bank:arg => B.reblock.destination (((Z).resetNames T).symm (.inr bank))
local notation "hostAt" bank:arg => (B.next.placement.pos (bankSite bank)).2
local notation "hh" bank:arg => (B.next.vertex (hostAt bank)).castLE B.next.valid.host
local notation "band" bank:arg => (B.next.placement.pos (bankSite bank)).1
local notation "pos" bank:arg => B.next.placement.block (bankSite bank)
open DescentResetStemWord DescentResetStemCompactOrder DescentIssuedFallbackPanel
open DescentPrimitivePalette
local notation "nativeH" => (S.hostSize (age+1))

/-- Read both chronological coordinates and the old host directly from the
charged public menu at the reached good bank. -/
theorem DateInputs.good_menu_coordinates (_dd:venue.degree=D) (cd:input.placement.cap=cap)
    (shape : config=K) (positive:0<cap) (R:(u).MeasuredChannels (Fintype.card B.next.V)) (dst:Memory w)
    (room:DateInputs.CaptureRoom R dst) (selfAt:CapturedSelf B (u) R)
    (side:Bool) (root:(Z).placement.Good) (cell:(DescentCommonPalette.rotor (Z).graph).Site)
    (menu:(deck_ (pos (born side root cell))).Values head_ gang_)
    (paid:(deck_ (pos (born side root cell))).casts.bits=(C₀).fallbackBits)
    (packets:rows_ (pos (born side root cell)))
    (issued:menu=(u).issuedPublicValues (pos (born side root cell)) R B.frame.basis rfl rfl rfl rfl rfl rfl
      menu.active menu.register packets) :
    let bank:=born side root cell
    let rawValue:=rawAt (pos bank) (hh bank) (band bank) menu paid
    let row:=Config.relabel shape B.dimension.symm rawValue
    let old:=B.frame.host.symm root.val.1
    ((K).oldConfig.header ((K).basic row) 3).val=
      hostCode (compress (hostDomain input.placement input.vertex old) (input.vertex old).val)
        (decide (old∉input.placement.near old)) ∧
    ∀(j:Fin (2^res*(2*input.placement.cap))) (axis:Fin 2),
      ((K).oldConfig.digit ((K).basic row) j (axis.castLE (by decide))).val=
        (coords B nativeH M rotor).value B.frame.basis axis.castSucc (pos bank)
          ((finProdFinEquiv.symm j : Fin (2^res)×Fin (2*input.placement.cap)).1.cast
            (congrArg (fun z=>2^(z-(T).commonDepth)) B.keyWidth)) (band bank) :=by
  intro bank rawValue row old
  have cuts:=ResetOutput.fromBoard_tree_caps G S board k tail age p f g drift degree payload e previous M nextM
    C packet prior_ base₀ positive
  obtain ⟨headVal,_,digitVal,_⟩:=Config.good_native_row shape B.dimension.symm rawValue
  have selfSmall : DescentResetPeerJointPacked.Aux.value (v).front.peer.shapes R.names R.prior R.near (hh bank) 3<
      2^(v).sheets.metaBits :=
    DescentResetPeerJointPacked.Aux.value_lt _ _ _ _ _ 3 room.distinct room.shapes room.keys room.previousSelf
  constructor
  · have rawSelf:=(u).public_tree_host (pos bank) R B.frame.basis rfl rfl rfl rfl rfl rfl packets
      menu paid issued (hh bank) (band bank) selfSmall (selfSmall.trans_le (Nat.pow_le_pow_right (by decide) cuts.2.2))
    exact (headVal 3).trans (rawSelf.trans ((selfAt B.next.valid.host (hh bank)).trans
      (bank_self_word B B.next.valid.host bank)))
  · intro j axis
    let lo:=(finProdFinEquiv.symm j : Fin (2^res)×Fin (2*input.placement.cap)).1
    have resEq : res=k:=by rw [B.keyWidth,B.commonDepth];omega
    have half : (2*cap)/2=cap:=by omega
    have cap₀ : (config).oldCap=input.placement.cap:=half.trans cd.symm
    have total : (config).oldConfig.count=2^res*(2*input.placement.cap):=by
      change 2^k*(2*(config).oldCap)=_;rw [cap₀,resEq]
    let ix:=j.cast total.symm
    let d₀:=(finProdFinEquiv.symm ix : Fin (config).donors×Fin (2*(config).oldCap)).1
    have address : d₀.val=lo.val:=by change j.val/(2*(config).oldCap)=j.val/(2*input.placement.cap);rw [cap₀]
    have limit : d₀.val<2^(co).residual:=by
      change d₀.val<2^k
      exact (address.trans_lt lo.isLt).trans_le (le_of_eq (congrArg (2^·) resEq))
    have digit:=((co).donor_bound B.frame.basis axis (pos bank) ⟨_,limit⟩ (band bank))
    have bound : (co).value B.frame.basis axis.castSucc (pos bank) ⟨d₀.val,limit⟩ (band bank)≤2^k:=by
      simpa only [show (co).residual=k from rfl,show (co).fine=k from rfl,max_self] using digit
    have got:=(u).public_tree_donor (pos bank) R B.frame.basis rfl rfl rfl rfl rfl rfl packets menu paid issued
      (hh bank) (band bank) ix axis (pos bank).isLt limit (bound.trans_lt cuts.1) (bound.trans_lt cuts.2.1)
    have dimOld : rgeom=k:=by rw [B.commonDepth];omega
    exact (digitVal j ix rfl (axis.castLE (by decide))).trans (got.trans
      (DescentStemCoordinateBook.Shape.value_relabel rfl rfl dimOld.symm rfl B.frame.basis B.frame.basis HEq.rfl
        _ _ _ rfl _ _ address _ _ rfl))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
