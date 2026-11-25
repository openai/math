import OAI.Hierarchy.DescentNamedGoodControlRegisters
import OAI.Hierarchy.DescentReachedMountedRotorSpan
import OAI.Hierarchy.DescentNamedPublicSocketConfig
import OAI.Hierarchy.DescentMeasuredBankLocation

namespace OAI
/-! # The named public operand span at each true postreset rotor node -/
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
local notation "laneWidth_" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
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
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx
local notation "HH" => S.hostSize age

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage

local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (roster (Z).graph res (GroupStage.depthBound D n f g)).card
local notation "U" => (v).actor

open DescentSortedRoster

open CandidateFront ClosedReset.Window DescentSortedRoster DescentResetLocalRoster DescentResetCandidatePair
open DescentFallbackPeriod.Projected DescentResetRankedWindows DescentResetOriginalSlots DescentContactDonorFront
open DescentPackedPrivateMenu DescentResetGates DescentGL
open DescentSharedCableNames
open DescentResetTrunks
local notation "C₀" => (v).setup
local notation "H₁" => S.hostSize (age+1)

local notation "ctrl" => (v).controlRegisters
local notation "controlStart" => (v).controlFloor base₀
local notation "liveAt" x:arg => (ctrl).live controlStart (x:Fin (v).receiver.blocks).val
local notation "regsAt" x:arg => (ctrl).ports controlStart ((a).c/2) (x:Fin (v).receiver.blocks).val
  ((U).directory actorBase).inverse ((U).depths actorBase) ((U).levels actorBase)
local notation "deck" x:arg => OperandMenu.publicPorts («a»:=a) sh start count io.hubs g (2^n) (liveAt x) (regsAt x)

local notation "cfg" => publicOperands (u).atlas (u).roots (u).menu.payload
local notation "operandValues" x:arg menu:arg => (u).menu.publicData sh start count io.hubs g (2^n)
  (liveAt x) (regsAt x) menu rfl ((x):Fin (v).receiver.blocks).val

open ClosedReset.Window DescentResetControlRegisters DescentVenueQuantityPlanes
local notation "qbits" => (v).setup.rotorBits
local notation "occ" x:arg => fun h g=>actualBit B B.next.valid.host h g x
local notation "scaled" => (⟨quantityDims B 1 HH H₁ (2^e) M,qbits⟩ : DescentResetControlRegisters.Chart)


local notation "rootHost" => B.next.vertex.trans (Fin.castLEEmb B.next.valid.host)
local notation "oldRank" => B.frame.host.symm.toEmbedding.trans idx
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "shapeWord" v₁:arg => ((Z).hostFields T oldRank v₁).2.val
local notation "levelAt" v₁:arg => (Z).placement.b (position (Z).graph (v₁).val)
local notation "receiver" => (C₀).placement
local notation "activeBit" row:arg => (cfg).oldConfig.header ((cfg).basic row) 0


open DescentSixParty.Chronology DescentKernelHistory DescentPrimitivePalette DescentLocalArchiveOrder DescentRetainedRangeDigits
open DescentResetPublicOperandBook
variable (hp : 0<p) (whole : p∣B.reset.unit) (priorArchive : Archive W) (earlier : Local priorArchive.bit)
local notation "m₀" => (Z).unit/p
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "fit" => (Nat.div_mul_cancel whole).symm
local notation "prog" => (Z).laneRecipe birth m₀ p hp fit
local notation "post" => (resetArchive B p hp whole priorArchive).bit
local notation "realOrder" => DescentLocalArchiveOrder.reset B p hp whole priorArchive earlier
local notation "K" => publicOperandConfig B qbits (C₀).queryBits M m₀ m₀ S.retainedNodes
  (S.retainedArgumentsAt G drift) p
local notation "badge" y:arg => (Z).localShape T (B.next.placement.pos (y).1).2
local notation "site" s:arg t:arg vtx:arg => (⟨(s,.inl t),DescentCommonPalette.rotorSiteEquiv (Z).graph d
  (DescentChosenRouter.selectedRotorLayers (Z).placement (Z).graph (Z).positive (Z).pay (Z).circuit s t)
  C (Z).width (Z).unit vtx⟩:(Z).bank.Site)
local notation "plan" s:arg t:arg vtx:arg => (Z).laneShape birth m₀ p hp fit (site s t vtx)
local notation "old" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation "room" => max 1 (max (Z).width (C*(Z).width))≤drift
local notation "blankAt" issued:arg => (issued).2.2.2.2.2.1
local notation "actualAt" issued:arg => (issued).2.2.2.2.2.2

set_option maxHeartbeats 1100000 in
include accepted in
/-- Reuse the public menu's authenticated register, directory, and packet reads. Every
old retained slab gives the same answer on this newly installed physical receiver. -/
theorem DateInputs.fromNamed_mounted_good_span (degreeAt : venue.degree=D)
    (capAt : input.placement.cap=cap) (calibrated : z=S.grainAt G.b p (age+1))
    (growth : G.b≤2^S.capGain) (wide : room)
    (s : Bool) (root : (Z).placement.Good) (cell : (DescentCommonPalette.rotor (Z).graph).Site)
    (gate : (prog (site s root cell)).Node) (y : NodeOrder.All post)
    (origin : resetOrigin B hp whole priorArchive y=.inr (.inr ⟨site s root cell,gate⟩))
    (name : Fin (Fintype.card B.next.V)→Fin (receiver).sparse)
    (ready : (u).Ready) (mem : Memory w)
    (publicRow : (deck (B.next.placement.block y.1)).Values (receiver).newHosts (receiver).groups)
    (issued : (u).PublicValuesRead ready mem (B.next.placement.block y.1) rfl name publicRow)
    (measureLive : ∀h gr,(publicRow.active h gr).val=((scaled).enabled (occ (B.next.placement.block y.1))
      (fun _=>1) h gr).val)
    (measure : ∀j h gr,(publicRow.register j h gr).val=((scaled).enabled (occ (B.next.placement.block y.1))
      (controlScalar B input.valid.host B.next.valid.host j) h gr).val)
    (arg : Fin (cfg).args) (node : Fin (cfg).nodes) (numbered : node.val=(realOrder y.1 y.2).val)
    (Y : Fin ((C₀).retained.outputs*(receiver).shapes)→Fin (receiver).oldHosts→
      Fin ((receiver).groups*(receiver).blocks)→Cell (C₀).retained.bits) (j : Fin (C₀).retained.outputs) :
    ∃shape:(cfg)=K,
      let x:=B.next.placement.block y.1
      let h₀:=rootHost (B.next.placement.pos y.1).2
      let g₀:=(B.next.placement.pos y.1).1
      let raw:=(operandValues x publicRow) h₀ g₀
      let recast:=Config.relabel shape B.dimension.symm raw
      GoodTapRows (p:=p) (field:=qbits) (query:=(C₀).queryBits) (lanes:=M) (nodes:=S.retainedNodes)
        (args:=S.retainedArgumentsAt G drift) (grain:=p) B s root recast →
        ∀axis:Fin 3, ((u).menu.spanValue name Y j x h₀ g₀ raw (finProdFinEquiv (arg,node)) (page axis)
          ((blankAt issued) h₀ g₀) ((actualAt issued) h₀ g₀)).val=atSlot (plan s root cell) gate arg.val axis :=by
  obtain ⟨graphAt,shapeAt⟩:=DateInputs.fromNamed_public_socket_config (B:=B) accepted drift degree payload
    e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut
    count previousMeta previousArguments initial prepared sceneRoom degreeAt capAt calibrated
  rw [←funded_units B accepted calibrated] at shapeAt
  refine ⟨shapeAt,?_⟩
  intro x h₀ g₀ raw recast rowsRead
  have occupied : actualBit B B.next.valid.host h₀ g₀ x≠0:=by
    have had : actualBit B B.next.valid.host h₀ g₀ x=1:=ite_eq_left ⟨y.1,rfl,rfl,rfl⟩
    rw [had];decide
  have place : position (Z).graph (B.next.placement.pos y.1).2.val=root.val.1:=
    congrArg Prod.fst (fresh_bank_location B hp whole priorArchive y ⟨site s root cell,gate⟩ origin)
  obtain ⟨live,_,depth,safe,ranked,_,_⟩:=DateInputs.named_good_registers (B:=B) accepted drift degree
    payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned
    fitsCut count previousMeta previousArguments initial prepared sceneRoom degreeAt capAt calibrated growth
    x publicRow measureLive measure s root _ g₀ place occupied
  have cells (j : Fin 4) : ((K).reg recast j).val=((cfg).reg raw j).val:=
    OperandMenu.register_relabel raw shapeAt B.dimension.symm j
  have badgeGood : OperandMenu.RotorBadge (Z).graph K recast:=
    ⟨badge y,(cells 3).trans ranked,fresh_excludes_primary B hp whole priorArchive y ⟨site s root cell,gate⟩ origin⟩
  have born:= (OperandMenu.RotorBadge.relabel_iff raw shapeAt B.dimension.symm rfl graphAt).mpr badgeGood
  let readField := fun axis : Fin 3 => ((u).menu.spanValue name Y j x h₀ g₀ raw (finProdFinEquiv (arg,node)) (page axis)
    ((blankAt issued) h₀ g₀) ((actualAt issued) h₀ g₀)).val
  have native : OperandMenu.MountedRotorLaw (u).atlas.board cfg raw node.val arg.val (C₀).fieldBits readField :=
    (u).menu.measured_mounted_at_badge name Y j x h₀ g₀ raw arg node ((blankAt issued) h₀ g₀)
    ((actualAt issued) h₀ g₀) born live
  have law : OperandMenu.MountedRotorLaw (Z).graph K recast node.val arg.val (C₀).fieldBits readField :=
    OperandMenu.MountedRotorLaw.relabel native shapeAt B.dimension.symm rfl graphAt
  rw [numbered] at law
  have two : 2<2^(C₀).fieldBits:=by
    have bound : 2≤(C₀).fieldBits:=by
      change 2≤ max (max (max 2 _) _) _
      exact ((Nat.le_max_left ..).trans (Nat.le_max_left ..)).trans (Nat.le_max_left ..)
    exact (by decide : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) bound)
  exact reached_mounted_span B hp whole priorArchive earlier s root cell accepted (age+1) calibrated growth gate y
    origin arg.val recast _ law rowsRead ((cells 1).trans depth) (by rw [cells 2,safe])
    ((cells 3).trans ranked) two (fun axis=>(B.fresh_range_room hp whole drift degree payload e previous M nextM
      old base₀ wide (site s root cell) gate arg.val axis).2) (le_refl _)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
