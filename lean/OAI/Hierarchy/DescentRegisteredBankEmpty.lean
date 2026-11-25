import OAI.Hierarchy.DescentIssuedMountedGoodAbsent
import OAI.Hierarchy.DescentIssuedMountedFallAbsent
import OAI.Hierarchy.DescentReachedBankPadding
import OAI.Hierarchy.DescentIssuedRangeRequests
import OAI.Hierarchy.DescentNamedOperandWordRoom
import OAI.Hierarchy.DescentRegisteredRangeRequests

namespace OAI
/-! # The issued zero operand count of an occupied device with an empty node slot -/
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
open DescentDatedPriorOperand DescentDatedAddressBook DescentSixParty.Chronology DescentPaidResidentCount
open DescentLocalArchiveOrder DescentKernelHistory DescentRetainedRangeDigits

local notation "r₀" => (C₀).retained
local notation "Rports" => DatePorts.reset a start u
local notation "L" => (Rports).rangeLayout
local notation:max "rangeCalls" dd:arg cd:arg ready:arg archived:arg μ:arg measured:arg dst:arg => DateInputs.RangeRequestsAt (B:=B) drift degree
  payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut
  count previousMeta previousArguments initial prepared sceneRoom dd cd ready archived μ measured dst

set_option hygiene true
set_option maxHeartbeats 1600000
set_option maxRecDepth 6144
/-- All seven selections share the genuinely mounted menu even at an occupied
actor whose requested node ordinal is beyond the device program. -/
private def emptyBankMenu (prepared : (rc).PreparedFits book)
    (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (hp : 0<p) (whole : p∣(Z).unit)
    (ready:(u).Ready) (dst:Memory w) (bank:(Z).bank.Site) : Prop :=
  ∃(size:HH*rows=(C₀).placement.sparse) (menu:(deck_ (pos bank)).Values head_ gang_)
    (reads:(u).PublicValuesRead ready dst (pos bank) rfl (fun j=>((Z).rawAtIndex T rank j).cast size) menu),
    ∀(arg:Fin (config).args) (node:Fin (config).nodes),Fintype.card (prg bank).Node≤node.val →
    ∀(Y:Fin ((C₀).retained.outputs*(C₀).placement.shapes)→Fin (C₀).placement.oldHosts→
      Fin ((C₀).placement.groups*(C₀).placement.blocks)→Cell (C₀).retained.bits) (j:Fin (C₀).retained.outputs)
      (axis:Fin 3),
      ((kept menu (pos bank) (fun t=>((Z).rawAtIndex T rank t).cast size) (hh bank) (band bank) Y j arg node)
        (page axis) ((blankAt reads) (hh bank) (band bank)) ((locatedAt reads) (hh bank) (band bank))).val=0

set_option hygiene false
local notation "after_" => (resetArchive B p hp whole oldA).bit
local notation "ordinal_" => DescentLocalArchiveOrder.reset B p hp whole oldA oldNum
local notation:max "rawX" axes:arg x:arg => ((x):Fin (L).blocks).cast (congrArg DescentDatedPriorOperand.Layout.blocks axes)
local notation:max "rawH" axes:arg x:arg => ((x):Fin (L).hosts).cast (congrArg DescentDatedPriorOperand.Layout.hosts axes)
local notation:max "rawG" axes:arg x:arg => ((x):Fin (L).groups).cast (congrArg DescentDatedPriorOperand.Layout.groups axes)
local notation:max "rawJ" axes:arg ok:arg x:arg => (((x):Fin (L).operands).cast (congrArg DescentDatedPriorOperand.Layout.operands axes)).cast
  (ok : (u).Ready).slots.symm
local notation:max "rawN" axes:arg ok:arg x:arg => (((x):Fin (L).nodes).cast (congrArg DescentDatedPriorOperand.Layout.nodes axes)).cast
  (ok : (u).Ready).nodes.symm

set_option hygiene true
include accepted in
theorem DateInputs.registered_bank_empty
    (prepared : (rc).PreparedFits book)
    (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (hp : 0<p) (whole : p∣(Z).unit) (oldA:Archive W) (oldNum:Local oldA.bit)
    (dd:venue.degree=D) (cd:input.placement.cap=cap)
    (gr:z=S.grainAt G.b p (age+1)) (growth:G.b≤2^S.capGain) (elapsed:0<age) (sorted:SourceSorted W input.order)
    (ready:(u).Ready) (mem:Memory w) (archived:(r₀).Values) (μ:DescentGL.Layout (E).dim) (measured dst:Memory w)
    (atDate:rowsAt dd ready mem cd μ measured dst) (requests:rangeCalls dd cd ready archived μ measured dst)
    (small:2*(v).receiver.candidates<2^(v).receiver.queryBits) (axes:(L)=(v).rangeLayout)
    (choices:∀i,DatePorts.OrdinalRead u ready small dst i) (places:DatePorts.RangeRoom Rports B.next after_)
    (x:Fin (L).blocks) (j:Fin (L).operands) (h₁:Fin (L).hosts) (g₁:Fin (L).groups) (n₁:Fin (L).nodes)
    (active:h₁.val<Fintype.card B.next.V) (bank:(Z).bank.Site)
    (located:occupies B.next.placement (Equiv.refl _) B.next.vertex ⟨h₁.val,active⟩
      (g₁.cast places.groups.symm) (x.cast (congrArg (2^·) places.radix.symm)) (bankSite bank))
    (missing:DatePorts.slotAt Rports B.next after_ ordinal_ places x n₁ h₁ g₁=none) :
    ((choices ((v).operandOrdinal (u).operand (page (2:Fin 3)) (rawJ axes ready j) (rawX axes x) (rawN axes ready n₁))).amount
      (rawH axes h₁) (rawG axes g₁)).val=0 :=by
  have available : emptyBankMenu (B:=B) (drift:=drift) (degree:=degree) (payload:=payload) (e:=e)
      (previous:=previous) (M:=M) (nextM:=nextM) (oldLanes:=oldLanes) (primitiveLanes:=primitiveLanes)
      (printedBits:=printedBits) (venue:=venue) (io:=io) (floor:=floor) (w:=w) (fitsStencil:=fitsStencil)
      (fitsSigned:=fitsSigned) (fitsCut:=fitsCut) (count:=count) (previousMeta:=previousMeta)
      (previousArguments:=previousArguments) (initial:=initial) (prepared:=prepared) (sceneRoom:=sceneRoom)
      (hp:=hp) (whole:=whole) ready dst bank :=by
    rcases bank with ⟨⟨side,source⟩,cell⟩
    rcases source with root | tree
    · let rotorIso := DescentCommonPalette.rotorSiteEquiv (Z).graph d
        (DescentChosenRouter.selectedRotorLayers (Z).placement (Z).graph (Z).positive (Z).pay (Z).circuit side root)
        C (Z).width (Z).unit
      obtain ⟨bare,rfl⟩ := rotorIso.surjective cell
      exact DateInputs.issued_mounted_good_absent (B:=B) accepted drift degree payload e previous M nextM oldLanes
        primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
        initial prepared sceneRoom hp whole dd ready mem cd gr μ measured dst atDate growth side root bare
    · exact DateInputs.issued_mounted_fall_absent (B:=B) accepted drift degree payload e previous M nextM oldLanes
        primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
        initial prepared sceneRoom hp whole dd ready mem cd gr μ measured dst atDate elapsed sorted side tree cell
  obtain ⟨size,menu,reads,blank⟩:=available
  have padded:=bank_slot_padding B hp whole oldA oldNum Rports places x n₁ h₁ g₁ active bank located missing
  have sameX : rawX axes x=pos bank:=Fin.ext (congrArg Fin.val located.2.2).symm
  have sameH : rawH axes h₁=hh bank:=Fin.ext (congrArg Fin.val located.1).symm
  have sameG : rawG axes g₁=band bank:=Fin.ext (congrArg Fin.val located.2.1).symm
  obtain ⟨hdr,root,windows,signed_,geo,dim,size_,hub,tickets,loaded,moving,readMatrix,signs,controls,issued⟩:=requests
  have cash:=DateInputs.named_amount_rooms G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom ready
  let arg:=rawJ axes ready j
  let node:=rawN axes ready n₁
  let amountAt (blk : Fin (v).rangeLayout.blocks) (holder : Fin (v).rangeLayout.hosts)
      (group₀ : Fin (v).rangeLayout.groups) :=
    ((choices ((v).operandOrdinal (u).operand (page (2:Fin 3)) arg blk node)).amount holder group₀).val
  change amountAt (rawX axes x) (rawH axes h₁) (rawG axes g₁) = 0
  have transported : amountAt (rawX axes x) (rawH axes h₁) (rawG axes g₁)
      = amountAt (pos bank) (hh bank) (band bank) :=
    ((congrArg (fun blk => amountAt blk (rawH axes h₁) (rawG axes g₁)) sameX).trans
      (congrArg (fun holder => amountAt (pos bank) holder (rawG axes g₁)) sameH)).trans
      (congrArg (fun group₀ => amountAt (pos bank) (hh bank) group₀) sameG)
  apply transported.trans
  have selected:=issued (pos bank) arg node menu reads small
    (fun f₀=>choices ((v).operandOrdinal (u).operand f₀ arg (pos bank) node)) ready.placed.lanes cash.2.1 cash.2.2
    (2:Fin 3) (hh bank) (band bank)
  apply selected.trans
  exact congrArg (fun value : ℕ => (value : Cell (v).receiver.valueBits).val)
    (blank arg node padded _ _ (2 : Fin 3))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
