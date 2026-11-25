import OAI.Hierarchy.DescentIssuedMountedFallSpan
import OAI.Hierarchy.DescentIssuedMountedGoodSpan
import OAI.Hierarchy.DescentPostedRetainedSpans
import OAI.Hierarchy.DescentRegisterArchiveValues
import OAI.Hierarchy.DescentFreshArgumentRoom

namespace OAI
/-! # A genuine issued bank gate's range fields in the recorded ordinal receiver -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
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

local notation:max "rawAt" xx:arg hh:arg gg:arg menu:arg cut₀:arg => (u).menu.publicData (u).shape start (u).count (u).hub (u).g (u).Y
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

set_option maxHeartbeats 2600000
set_option maxRecDepth 8192
/-- All three native span words of one installed bank gate on its actual registered menu. -/
def DateInputs.BankRangeMenu (ready:(u).Ready) (dst:Memory w) (y:NodeOrder.All post)
    (bank:(Z).bank.Site) (gate:(prg bank).Node) : Prop :=
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
          (page axis) (by exact ((blankAt reads) host group_)) (by exact ((locatedAt reads) host group_))).val=
          atSlot (plan bank) gate arg.val axis
set_option hygiene false
open DescentBundleHistory DescentPacking.PackedMatch.Local.Stage DescentSixParty.Chronology
local notation "Rports" => DatePorts.reset a start u
local notation "amt" => (v).setup
local notation:max "ranges" dd:arg cd:arg ready:arg oldValues:arg μ:arg measured:arg actors:arg => DateInputs.RangeRequestsAt (B:=B) drift degree
  payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
  previousMeta previousArguments initial prepared sceneRoom dd cd ready oldValues μ measured actors
local notation:max "receipt" ready:arg dst:arg y:arg bank:arg gate:arg => DateInputs.BankRangeMenu (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom hp whole archive earlier ready dst y bank gate

variable {R:ℕ} (shape:WorldShape p R archive.bit) (one:1≤R) (positive:0<(Z).unit)
    (widthBound:max 1 (max (Z).width (C*(Z).width))≤R) (wordBound:max 1 (max (Z).width (C*(Z).width))≤drift)
local notation "shape₁" => reset_shape_at hp one B archive shape positive whole widthBound
local notation "prior" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
variable (ready:(u).Ready) (actors:Memory w) (small:2*(v).receiver.candidates<2^(v).receiver.queryBits)
    (axes:(Rports).rangeLayout=(v).rangeLayout) (choices:∀i,DatePorts.OrdinalRead (u) ready small actors i)
    (places:DatePorts.RangeRoom Rports B.next post) (dd:venue.degree=D) (cd:input.placement.cap=cap)
    (oldValues:(amt).retained.Values) (μ:DescentGL.Layout (E).dim) (measured:Memory w)
    (requests:ranges dd cd ready oldValues μ measured actors)
local notation "L" => (Rports).rangeLayout
local notation:max "rearg" j:arg => (((j:Fin (L).operands).cast (congrArg DescentDatedPriorOperand.Layout.operands axes)).cast ready.slots.symm)
local notation:max "renode" n:arg => (((n:Fin (L).nodes).cast (congrArg DescentDatedPriorOperand.Layout.nodes axes)).cast ready.nodes.symm)
local notation:max "reblock" x:arg => ((x:Fin (L).blocks).cast (congrArg DescentDatedPriorOperand.Layout.blocks axes))
local notation:max "rhost" h:arg => ((h:Fin (L).hosts).cast (congrArg DescentDatedPriorOperand.Layout.hosts axes))
local notation:max "rgrp" g:arg => ((g:Fin (L).groups).cast (congrArg DescentDatedPriorOperand.Layout.groups axes))

include requests wordBound in
theorem DateInputs.registered_bank_amount_of_menu (xb:Fin (L).blocks) (j:Fin (L).operands) (h₀:Fin (L).hosts)
    (g₀:Fin (L).groups) (n₀:Fin (L).nodes) (y:NodeOrder.All post) (bank:(Z).bank.Site) (gate:(prg bank).Node)
    (hit:DatePorts.slotAt Rports B.next post number places xb n₀ h₀ g₀=some y)
    (origin:resetOrigin B hp whole archive y=.inr (.inr ⟨bank,gate⟩))
    (acquired:receipt ready actors y bank gate) (axis:Fin 3) :
    ((choices ((v).operandOrdinal (u).operand (page axis) (rearg j) (reblock xb) (renode n₀))).amount
      (rhost h₀) (rgrp g₀)).val=atSlot ((shape₁).sites y.1) y.2 j.val axis:=by
  obtain ⟨hx,hn,rackAt,hg⟩:=DatePorts.slotAt_coordinates Rports B.next post number places xb n₀ h₀ g₀ y.1 y.2 hit
  let blk:=(B.next.placement.block y.1)
  let who:=(B.next.vertex (B.next.placement.pos y.1).2).castLE B.next.valid.host
  let bankGroup:=(B.next.placement.pos y.1).1
  have bx:(reblock xb)=blk:=by
    apply Fin.ext
    have e₀ := congrArg Fin.val hx
    exact e₀
  have host:(rhost h₀)=who:=Fin.ext (congrArg Fin.val rackAt)
  have grp:(rgrp g₀)=bankGroup:=Fin.ext (congrArg Fin.val hg)
  have ordinal:(renode n₀).val=(number y.1 y.2).val:=congrArg Fin.val hn
  let amountAt (block : Fin (v).receiver.blocks) (rack : Fin (v).receiver.hosts) (group : Fin (v).receiver.groups) : ℕ :=
    ((choices ((v).operandOrdinal (u).operand (page axis) (rearg j) block (renode n₀))).amount rack group).val
  have sameAmount : amountAt (reblock xb) (rhost h₀) (rgrp g₀) = amountAt blk who bankGroup :=
    (congrArg (fun b => amountAt b (rhost h₀) (rgrp g₀)) bx).trans
      ((congrArg (fun h => amountAt blk h (rgrp g₀)) host).trans (congrArg (amountAt blk who) grp))
  refine sameAmount.trans ?_
  obtain ⟨hdr,x,X,sig,geo,dim,size,hub,fees,root,moved,matrix,signed,shared,issued⟩:=requests
  obtain ⟨sizeAt,menu,read,bankWord⟩:=acquired
  have packed:=DateInputs.named_amount_rooms G S board k tail age p f g drift degree payload e previous M nextM
    C packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom ready
  have word:=issued blk (rearg j) (renode n₀) menu read small
      (fun f₀=>choices ((v).operandOrdinal (u).operand f₀ (rearg j) blk (renode n₀)))
      ready.placed.lanes packed.2.1 packed.2.2 axis who bankGroup
  let strips : (amt).retained.Strips := fun t => DescentSixParty.PackedFlow.Channels.blockValues geo.cut ((amt).retained.before geo.size oldValues t) (cast (congrArg DescentGL.Layout dim) μ)
  let bankData := (amt).assignedDigits geo.host geo.groups (u).bank.which X strips
  let output := (amt).retained.outputID 1 (page axis) (rearg j) (renode n₀)
  have nativeWord := bankWord (rearg j) (renode n₀) ordinal bankData output axis
  have room : atSlot (plan bank) gate j.val axis<2^(v).receiver.valueBits:=
    (B.fresh_range_room hp whole drift degree payload e previous M nextM prior base₀ wordBound bank gate j.val axis).1
  have ff:=reset_range_origin B hp whole archive shape one positive widthBound y
  change (shape₁).nodeFields y=_ at ff
  rw [origin] at ff
  change ((shape₁).sites y.1).sliceFields y.2=(plan bank).sliceFields gate at ff
  have nativeNat := (congrArg (fun v₀ : ℕ => (v₀ : Cell (v).receiver.valueBits).val) nativeWord).trans
    (Fin.val_cast_of_lt room)
  exact (word.trans nativeNat).trans (DescentRetainedRangeDigits.of_fields (plan bank) gate ((shape₁).sites y.1) y.2 ff.symm j.val axis)

include accepted requests wordBound in
theorem DateInputs.registered_bank_spans (m:Memory w) (gr:z=S.grainAt G.b p (age+1))
    (original:rowsAt dd ready m cd μ measured actors) (base:G.b≤2^S.capGain)
    (elapsed:0<age) (sorted:SourceSorted W input.order) [Fintype X] :
    DatePorts.SevenOriginSpans (u) B.next post number places shape₁ ready small axes actors choices
      (resetOrigin B hp whole archive) (Sum.inr ∘ Sum.inr):=by
  intro xb j axis h₀ g₀ n₀ y hit admissible bankGate origin
  rcases bankGate with ⟨bank,gate⟩
  refine DateInputs.registered_bank_amount_of_menu (B:=B) (drift:=drift) (degree:=degree) (payload:=payload) (e:=e)
    (previous:=previous) (M:=M) (nextM:=nextM) (oldLanes:=oldLanes) (primitiveLanes:=primitiveLanes)
    (printedBits:=printedBits) (venue:=venue) (io:=io) (floor:=floor) (w:=w) (fitsStencil:=fitsStencil)
    (fitsSigned:=fitsSigned) (fitsCut:=fitsCut) (count:=count) (previousMeta:=previousMeta)
    (previousArguments:=previousArguments) (initial:=initial) (prepared:=prepared) (sceneRoom:=sceneRoom) (hp:=hp)
    (whole:=whole) (archive:=archive) (earlier:=earlier) (ready:=ready) (actors:=actors) (small:=small) (dd:=dd)
    (cd:=cd) (oldValues:=oldValues) (μ:=μ) (measured:=measured) (requests:=requests) (wordBound:=wordBound)
    (choices:=choices) (axes:=axes) (places:=places) (shape:=shape) (one:=one) (positive:=positive)
    (widthBound:=widthBound) (xb:=xb) (j:=j) (h₀:=h₀) (g₀:=g₀) (n₀:=n₀) (y:=y) (bank:=bank) (gate:=gate) (hit:=hit)
    (origin:=origin) (axis:=axis) (acquired:=?_)
  rcases bank with ⟨⟨side,source⟩,place⟩
  cases source with
  | inl root =>
    let rotorIso := DescentCommonPalette.rotorSiteEquiv (Z).graph d
      (DescentChosenRouter.selectedRotorLayers (Z).placement (Z).graph (Z).positive (Z).pay (Z).circuit side root) C (Z).width (Z).unit
    obtain ⟨physical,rfl⟩ := rotorIso.surjective place
    exact DateInputs.issued_mounted_good_span (B:=B) accepted drift degree payload e previous M nextM
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
      previousArguments initial prepared sceneRoom hp whole archive earlier dd ready m cd gr μ measured actors
      original base elapsed sorted wordBound side root physical gate y origin
  | inr tree =>
    exact DateInputs.issued_mounted_fall_span (B:=B) accepted drift degree payload e previous M nextM
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
      previousArguments initial prepared sceneRoom hp whole archive earlier dd ready m cd gr μ measured actors
      original elapsed sorted side tree place gate y origin


end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
