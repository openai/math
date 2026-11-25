import OAI.Hierarchy.DescentNamedGoodObservation
import OAI.Hierarchy.DescentNamedMountedGoodSpan

namespace OAI
/-! # Original menu publication for all three span digits at a reached, installed rotor -/
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
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤(laneBits ((S.groupWidth k tail age)+k) payload (S.localWalshBits p ((S.groupWidth k tail age)+k) f (quota S.rounds)))-k) (fitsSigned : e≤previous) (fitsCut : previous≤(S.groupWidth k tail age)) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "E" => (a).estimator start
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
local notation "rows" => (DescentDenseHostOrder.roster (Z).graph res (GroupStage.depthBound D n f g)).card
local notation "U" => (v).actor

open DescentSortedRoster
local notation:max "imageOf" degreeAt:arg capAt:arg => fromNamed_root_image (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt

open CandidateFront ClosedReset.Window DescentSortedRoster DescentResetLocalRoster DescentResetCandidatePair
open DescentFallbackPeriod.Projected DescentResetRankedWindows DescentResetOriginalSlots DescentContactDonorFront
open DescentPackedPrivateMenu DescentResetGates DescentGL
open ClosedReset.Window DescentResetControlRegisters DescentVenueQuantityPlanes
local notation "height₁" => S.hostSize (age+1)
local notation "group₁" => S.groupCount (age+1)
local notation "qbits" => (v).setup.rotorBits
local notation "control" => (v).controlRegisters
local notation "first_" => (v).controlFloor base₀
local notation:max "occ" x:arg => fun h g=>actualBit B B.next.valid.host h g x
local notation "scaled" => (⟨quantityDims B 1 HH height₁ (2^e) M,qbits⟩ : Chart)

local notation "C₀" => (v).setup
local notation:max "stage_" x:arg => (control).live first_ (x:DescentColonies.Block k).val
local notation:max "regs_" x:arg => (control).ports first_ ((a).c/2) (x:DescentColonies.Block k).val ((U).directory actorBase).inverse
  ((U).depths actorBase) ((U).levels actorBase)
local notation:max "deck_" x:arg => OperandMenu.publicPorts («a»:=a) sh start count io.hubs g (2^n) (stage_ x) (regs_ x)
local notation "head_" => (C₀).placement.newHosts
local notation "gang_" => (C₀).placement.groups
local notation:max "rows_" x:arg => (b₀:Bool)→Fin ((deck_ x).packets.stage 0 b₀).fields→Fin (deck_ x).packets.blocks→
  Fin head_→Fin gang_→Cell ((deck_ x).casts.width 0)

open DescentPaidResidentCount.Reset DescentResetPublicOperandBook
local notation "rotor" => (v).setup.rotorBits
local notation "q₁" => (v).setup.queryBits
local notation "config" => publicOperands (u).atlas (u).roots (u).menu.payload
local notation "snapAt" => PaddedSnapshot B input.valid.host (v).middle.rootField

local notation:max "rawAt" xx:arg hh:arg gg:arg menu:arg cut₀:arg => (u).menu.publicData sh start count io.hubs g (2^n)
  (stage_ xx) (regs_ xx) menu cut₀ (xx:DescentColonies.Block k).val hh gg

local notation "unit" => (Z).unit/p
local notation "K" => publicOperandConfig B rotor q₁ M unit unit S.retainedNodes (S.retainedArgumentsAt G drift) p
local notation:max "born" s:arg root:arg cell:arg => (⟨(s,.inl root),DescentCommonPalette.rotorSiteEquiv (Z).graph d
  (DescentChosenRouter.selectedRotorLayers (Z).placement (Z).graph (Z).positive (Z).pay (Z).circuit s root)
  C (Z).width (Z).unit cell⟩ : (Z).bank.Site)
local notation:max "bankSite" bank:arg => B.reblock.destination (((Z).resetNames T).symm (.inr bank))
local notation:max "hostAt" bank:arg => (B.next.placement.pos (bankSite bank)).2
local notation:max "hh" bank:arg => (B.next.vertex (hostAt bank)).castLE B.next.valid.host
local notation:max "band" bank:arg => (B.next.placement.pos (bankSite bank)).1
local notation:max "pos" bank:arg => B.next.placement.block (bankSite bank)
open DescentResetStemWord DescentResetStemCompactOrder DescentIssuedFallbackPanel
open DescentPrimitivePalette
local notation "nativeH" => (S.hostSize (age+1))

open DescentRotorWindowArchive DescentIssuedFallbackPanel DescentPrimitivePalette
local notation:max "srcRow" bank:arg menu:arg paid:arg => rawAt (pos bank) (hh bank) (band bank) menu paid
local notation "cross" => congrArg (fun size=>DescentRotorWindowArchive.count input.placement.degree size input.placement.cap)
  (congrArg (fun size=>2^(size-(T).commonDepth)) B.keyWidth)
local notation:max "seenAt" row:arg bank:arg => FreshObservation (p:=p) (field:=rotor) (query:=q₁) (lanes:=M)
  (nodes:=S.retainedNodes) (args:=S.retainedArgumentsAt G drift) B row (.inr bank)
local notation "candidate" => (v).receiver
local notation:max "rowsAt" dd:arg ready:arg mem:arg cd:arg μ:arg measured:arg dst:arg => DateInputs.OriginalPublicRowsAt (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom dd ready mem cd μ measured dst
local notation:max "observed" ready:arg dst:arg block:arg size:arg shape:arg rh:arg rg:arg law:arg => DateInputs.ObservedFreshRow (B:=B) drift degree payload e
  previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
  previousMeta previousArguments initial prepared sceneRoom ready dst block size shape rh rg law


open DescentSixParty.Chronology DescentLocalArchiveOrder DescentKernelHistory DescentRetainedRangeDigits
variable (hp : 0<p) (whole : p∣B.reset.unit) (archive : Archive W) (earlier : Local archive.bit)
local notation "key" => DescentOrderedReset.grains W B.count B.order
local notation "fit" => (Nat.div_mul_cancel whole).symm
local notation "prg" => (Z).laneRecipe key unit p hp fit
local notation "post" => (resetArchive B p hp whole archive).bit
local notation "number" => DescentLocalArchiveOrder.reset B p hp whole archive earlier
local notation:max "plan" bank:arg => (Z).laneShape key unit p hp fit bank
local notation:max "kept" menu_:arg xx:arg id_:arg rr:arg gg:arg Y:arg j:arg arg:arg node:arg => (u).menu.spanValue id_ Y j xx rr gg
  (rawAt xx rr gg menu_ rfl) (finProdFinEquiv (arg,node))
local notation:max "blankAt" seen:arg => (seen).2.2.2.2.2.1
local notation:max "locatedAt" seen:arg => (seen).2.2.2.2.2.2

include accepted hp whole in
/-- All flattened slots, including padding, are read against one and the same genuine
actuator packet and its original public comparison matrix. -/
theorem DateInputs.issued_mounted_good_span (dd:venue.degree=D) (ready:(u).Ready) (mem:Memory w)
    (cd:input.placement.cap=cap) (gr:z=S.grainAt G.b p (age+1)) (μ:DescentGL.Layout (E).dim) (measured dst:Memory w)
    (atDate:rowsAt dd ready mem cd μ measured dst) (growth:G.b≤2^S.capGain)
    (elapsed:0<age) (sorted:SourceSorted W input.order) («wide»:max 1 (max (Z).width (C*(Z).width))≤drift)
    (side:Bool) (root:(Z).placement.Good) (cell:(DescentCommonPalette.rotor (Z).graph).Site)
    (gate:(prg (born side root cell)).Node) (y:NodeOrder.All post)
    (origin:resetOrigin B hp whole archive y=.inr (.inr ⟨born side root cell,gate⟩)) :
    let x:=B.next.placement.block y.1
    let host:=(B.next.vertex (B.next.placement.pos y.1).2).castLE B.next.valid.host
    let group_:=(B.next.placement.pos y.1).1
    ∃(size:HH*rows=(C₀).placement.sparse) (menu:(deck_ x).Values head_ gang_)
      (reads:(u).PublicValuesRead ready dst x rfl (fun j=>((Z).rawAtIndex T rank j).cast size) menu),
      ∀(arg:Fin (config).args) (node:Fin (config).nodes),node.val=(number y.1 y.2).val →
      ∀(Y:Fin ((C₀).retained.outputs*(C₀).placement.shapes)→Fin (C₀).placement.oldHosts→
        Fin ((C₀).placement.groups*(C₀).placement.blocks)→Cell (C₀).retained.bits) (j:Fin (C₀).retained.outputs)
        (axis:Fin 3),
        ((kept menu x (fun t=>((Z).rawAtIndex T rank t).cast size) host group_ Y j arg node)
          (page axis) (blankAt reads host group_) (locatedAt reads host group_)).val=
          atSlot (plan (born side root cell)) gate arg.val axis:=by
  let bank:=born side root cell
  rcases y with ⟨location,gateAt⟩
  have eqAt:=reached_node_site B hp whole archive ⟨location,gateAt⟩
  rw [origin] at eqAt
  change bankSite bank=location at eqAt
  subst location
  intro x host group_
  have positive : 0<HH:=Nat.zero_lt_of_lt (idx (B.frame.host.symm root.val.1)).isLt
  obtain ⟨R,capture,selfAt,hRaw,sRaw,xCount,all⟩:=DateInputs.fromNamed_public_recorded_matrix_at
    (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil
    fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom dd ready mem cd μ measured dst atDate positive
  obtain ⟨menu,paid,source,active,registers,packets,issued,_,_,hdr,xs,rootRead,groupAt,fs,ms,reads⟩:=all x
  refine ⟨congrArg₂ Nat.mul hRaw sRaw,menu,source,?_⟩
  intro arg node numbered Y j
  obtain ⟨shape,useSpan⟩:=DateInputs.fromNamed_mounted_good_span (B:=B) accepted drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom hp whole archive earlier dd cd gr growth «wide» side root cell gate ⟨bankSite bank,gateAt⟩
    origin _ ready dst menu source active registers arg node numbered Y j
  let acquired:=imageOf dd cd
  let snap:=DescentPaidResidentCount.Reset.root_snapshot B input.valid.host acquired.receiver acquired.book acquired.prepared measured hdr xs
  have sensed:=DateInputs.named_good_observation_of_menu (B:=B) accepted drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom dd cd gr growth elapsed sorted shape R dst capture selfAt side root cell menu paid packets issued
    active registers positive snap groupAt ms (fun i=>((reads host group_).2 i).2)
  exact useSpan sensed.2.2.1

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
