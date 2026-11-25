import OAI.Hierarchy.DescentIssuedMountedGoodSpan
import OAI.Hierarchy.DescentMountedRotorAbsent
import OAI.Hierarchy.DescentMeasuredBankBadge

namespace OAI
/-! # Padded primitive rows on a physically occupied good bank -/
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
  (venue : StageVenueTail.Date) (io : Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
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
variable (previousMeta previousArguments : ℕ) (initial : Bool)
local notation "datedInput" pr:arg sc:arg => I₀ previousMeta previousArguments initial pr sc
set_option hygiene false
local notation "u" => datedInput prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx

local notation "HH" => S.hostSize age
local notation "nBits" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "tBits" => 2*k+n+2


open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage











local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (roster (Z).graph res (GroupStage.depthBound D n f g)).card

local notation "U" => (v).actor
local notation "dir" => (U).directory actorBase
local notation "scene" => (U).scene actorBase
local notation "pub" => (((rc).preparedRoots book prepared).seq ((U).classifier (u).actor actorBase w)).seq ((dir).program w scene)
local notation "ticks" => ((rc).preparedTicks book prepared+(U).classifierTime (u).actor actorBase w)+(dir).ticks scene

local notation "entry₀" => (a).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)

open DescentSortedRoster
local notation "imageOf" degreeAt:arg capAt:arg => fromNamed_root_image (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "heldRoot" degreeAt:arg capAt:arg measured:arg =>
  (∃hdr : DescentPaidResidentCount.Reset.OriginalHeader B input.valid.host (imageOf degreeAt capAt).receiver
        (imageOf degreeAt capAt).book measured,
    ∃x : DescentPaidResidentCount.Reset.OriginalArrays B input.valid.host (v).middle.rootField,
      ClosedReset.Window.RootPacket B (imageOf degreeAt capAt).receiver (imageOf degreeAt capAt).book
        (imageOf degreeAt capAt).prepared measured hdr (imageOf degreeAt capAt).sources x nBits tBits)

open CandidateFront ClosedReset.Window DescentSortedRoster DescentResetLocalRoster DescentResetCandidatePair
open DescentFallbackPeriod.Projected DescentResetRankedWindows DescentResetOriginalSlots DescentContactDonorFront
open DescentPackedPrivateMenu DescentResetGates DescentGL









open ClosedReset.Window DescentResetControlRegisters DescentVenueQuantityPlanes
local notation "height₁" => S.hostSize (age+1)

local notation "qbits" => (v).setup.rotorBits
local notation "control" => (v).controlRegisters
local notation "first_" => (v).controlFloor base₀


local notation "occ" x:arg => fun hostIndex groupIndex=>actualBit B B.next.valid.host hostIndex groupIndex x
local notation "scaled" => (⟨quantityDims B 1 HH height₁ (2^e) M,qbits⟩ : DescentResetControlRegisters.Chart)


local notation "C₀" => (v).setup

local notation "stage_" x:arg => (control).live first_ (x:DescentColonies.Block k).val
local notation "regs_" x:arg => (control).ports first_ ((a).c/2) (x:DescentColonies.Block k).val ((U).directory actorBase).inverse
  ((U).depths actorBase) ((U).levels actorBase)
local notation "deck_" x:arg => OperandMenu.publicPorts («a»:=(a)) sh start count io.hubs g (2^n) (stage_ x) (regs_ x)
local notation "head_" => (C₀).placement.newHosts
local notation "gang_" => (C₀).placement.groups
local notation "rows_" x:arg => (b₀:Bool)→Fin ((deck_ x).packets.stage 0 b₀).fields→Fin (deck_ x).packets.blocks→
  Fin head_→Fin gang_→Cell ((deck_ x).casts.width 0)


open DescentPaidResidentCount.Reset DescentResetPublicOperandBook
local notation "rotor" => (v).setup.rotorBits
local notation "q₁" => (v).setup.queryBits
local notation "config" => publicOperands (u).atlas (u).roots (u).menu.payload


local notation "rawAt" xx:arg hh:arg gg:arg menu:arg cut₀:arg => (u).menu.publicData sh start count io.hubs g (2^n)
  (stage_ xx) (regs_ xx) menu cut₀ (xx:DescentColonies.Block k).val hh gg

local notation "unit" => (Z).unit/p
local notation "K" => publicOperandConfig B rotor q₁ M unit unit S.retainedNodes (S.retainedArgumentsAt G drift) p
local notation "born" s:arg root:arg cell:arg => (⟨(s,.inl root),
  DescentCommonPalette.rotorSiteEquiv (Z).graph d
    (DescentChosenRouter.selectedRotorLayers (Z).placement (Z).graph (Z).positive (Z).pay (Z).circuit s root)
    C (Z).width (Z).unit cell⟩ : (Z).bank.Site)
local notation "bankSite" bank:arg => B.reblock.destination (((Z).resetNames T).symm (.inr bank))
local notation "hostAt" bank:arg => (B.next.placement.pos (bankSite bank)).2
local notation "hh" bank:arg => (B.next.vertex (hostAt bank)).castLE B.next.valid.host
local notation "band" bank:arg => (B.next.placement.pos (bankSite bank)).1
local notation "pos" bank:arg => B.next.placement.block (bankSite bank)
open DescentPrimitivePalette
local notation "rowsAt" dd:arg ready:arg mem:arg cd:arg μ:arg measured:arg dst:arg => DateInputs.OriginalPublicRowsAt (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom dd ready mem cd μ measured dst
open DescentSixParty.Chronology DescentLocalArchiveOrder DescentKernelHistory DescentRetainedRangeDigits
local notation "key" => DescentOrderedReset.grains W B.count B.order
local notation "fit" => (Nat.div_mul_cancel whole).symm
local notation "prg" => (Z).laneRecipe key unit p hp fit
local notation "kept" menu_:arg xx:arg id_:arg rr:arg gg:arg Y:arg j:arg arg:arg node:arg => (u).menu.spanValue id_ Y j xx rr gg
  (rawAt xx rr gg menu_ rfl) (finProdFinEquiv (arg,node))
local notation "blankAt" seen:arg => (seen).2.2.2.2.2.1
local notation "locatedAt" seen:arg => (seen).2.2.2.2.2.2

open DescentChosenRouter DescentBaseProfile
set_option hygiene true
set_option maxHeartbeats 1600000
set_option maxRecDepth 6144
include accepted in
/-- An installed good actor remains visible in the physical directory even if it
has no operation at this ordinal. All three selected range inputDigits_ are zero. -/
theorem DateInputs.issued_mounted_good_absent
    (prepared : (rc).PreparedFits book)
    (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (hp : 0<p) (whole : p∣(Z).unit)
    (dd:venue.degree=D) (ready:(u).Ready) (mem:Memory w)
    (cd:input.placement.cap=cap) (gr:z=S.grainAt G.b p (age+1)) (μ:DescentGL.Layout (E).dim) (measured dst:Memory w)
    (atDate:rowsAt dd ready mem cd μ measured dst) (growth:G.b≤2^S.capGain)
    (side:Bool) (root:(Z).placement.Good) (cell:(DescentCommonPalette.rotor (Z).graph).Site) :
    let bank:=born side root cell
    let x:=pos bank
    let host:=hh bank
    let group_:=band bank
    ∃(size:HH*rows=(C₀).placement.sparse) (menu:(deck_ x).Values head_ gang_)
      (reads:(u).PublicValuesRead ready dst x rfl (fun j=>((Z).rawAtIndex T rank j).cast size) menu),
      ∀(arg:Fin (config).args) (node:Fin (config).nodes),Fintype.card (prg bank).Node≤node.val →
      ∀(Y:Fin ((C₀).retained.outputs*(C₀).placement.shapes)→Fin (C₀).placement.oldHosts→
        Fin ((C₀).placement.groups*(C₀).placement.blocks)→Cell (C₀).retained.bits) (j:Fin (C₀).retained.outputs)
        (axis:Fin 3),
        ((kept menu x (fun t=>((Z).rawAtIndex T rank t).cast size) host group_ Y j arg node)
          (page axis) ((blankAt reads) host group_) ((locatedAt reads) host group_)).val=0:=by
  intro bank x host group_
  have positive : 0<HH:=Nat.zero_lt_of_lt (idx (B.frame.host.symm root.val.1)).isLt
  obtain ⟨R,capture,selfAt,hRaw,sRaw,xCount,all⟩:=DateInputs.fromNamed_public_recorded_matrix_at
    (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil
    fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom dd ready mem cd μ measured dst atDate positive
  obtain ⟨menu,paid,source,active,registers,_⟩:=all x
  let size:=congrArg₂ Nat.mul hRaw sRaw
  let name:=fun t=>((Z).rawAtIndex T rank t).cast size
  refine ⟨size,menu,source,?_⟩
  have controls:=DateInputs.named_bank_good_registers (B:=B) accepted drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom dd cd gr growth side root cell menu active registers
  obtain ⟨live,_,depth,safe,ranked,layers,_⟩:=controls
  obtain ⟨graphAt,shapeAt⟩:=DateInputs.fromNamed_public_socket_config (B:=B) accepted drift degree payload
    e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut
    count previousMeta previousArguments initial prepared sceneRoom dd cd gr
  rw [←funded_units B accepted gr] at shapeAt
  let raw:=rawAt x host group_ menu rfl
  let recast:=Config.relabel shapeAt B.dimension.symm raw
  have register (j : Fin 4) : ((K).reg recast j).val=((config).reg raw j).val:=
    OperandMenu.register_relabel raw shapeAt B.dimension.symm j
  let badge:=(Z).localShape T (hostAt bank)
  have actual : badge.val=.good side ((),((Z).goodLabel T root).val.2) cell := by
    change ((Z).localShape T (hostAt bank)).val = _
    rw [(DescentPrimitivePalette.original_bank_actor B bank).2.2]
    simp only [bank, DescentCommonHost.bankNode, DescentDenseHostOrder.shape, Equiv.symm_apply_apply,
      DescentCanonicalPorts.short, DescentCanonicalPorts.relative, DescentSixParty.ResetInput.goodLabel]
  have good : OperandMenu.RotorBadge (Z).graph K recast:=⟨badge,(register 3).trans ranked,
    fun t h=>by rw [actual] at h;cases h⟩
  have badgeAt:=(OperandMenu.RotorBadge.relabel_iff raw shapeAt B.dimension.symm rfl graphAt).mpr good
  have layer:=sized_layer_count (Z).placement (Z).graph (Z).positive (Z).pay (Z).circuit unit p fit side root
  let sized := (fit ▸ (Z).circuit : Hardware («K»:=F) («C₀»:=C) («u»:=unit*p) (Z).placement (Z).graph (Z).positive (Z).pay)
  have resized := layer.trans (selectedRotorLayers_eq (Z).placement (Z).graph (Z).positive (Z).pay sized side root)
  intro arg node empty Y j axis
  let readField := fun coord : Fin 3 => ((u).menu.spanValue name Y j x host group_ raw
    (finProdFinEquiv (arg,node)) (page coord) ((blankAt source) host group_) ((locatedAt source) host group_)).val
  have native : OperandMenu.MountedRotorAbsentLaw (u).atlas.board config raw node.val readField :=
    (u).menu.measured_mounted_absent_at_badge name Y j x host group_ raw arg node
    ((blankAt source) host group_) ((locatedAt source) host group_) badgeAt live
  have law : OperandMenu.MountedRotorAbsentLaw (Z).graph K recast node.val readField :=
    OperandMenu.MountedRotorAbsentLaw.relabel native shapeAt B.dimension.symm rfl graphAt
  have zeroReg : ((K).reg recast 2).val = 0 := (register 2).trans safe
  apply law (Z).placement (Z).positive (Z).pay (Z).circuit key d hp fit side root cell badge
    ((Z).goodLabel T root) empty ((register 1).trans depth) (congrArg (fun n : ℕ => n%2) zeroReg)
    ((register 3).trans ranked) ((register 3).trans ranked) actual _ axis
  change DescentRecordedRotorLayers.layers (Z).n (Z).width f ((K).reg recast 0).val=_
  rw [register 0]
  exact layers.trans resized

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
