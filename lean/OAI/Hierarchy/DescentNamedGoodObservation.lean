import OAI.Hierarchy.DescentOriginalOperandLocation
import OAI.Hierarchy.DescentNamedGoodCoordinates
import OAI.Hierarchy.DescentNamedFreshMenus
import OAI.Hierarchy.DescentFreshOperandObservation
import OAI.Hierarchy.DescentGoodMatrixGathered
import OAI.Hierarchy.DescentOriginalWideMatrix
import OAI.Hierarchy.DescentResetMiddleFieldRoom
import OAI.Hierarchy.DescentNamedGoodControlRegisters
import OAI.Hierarchy.DescentReachedGoodTapRows
import OAI.Hierarchy.DescentNamedRecordedMatrixAt

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
variable (previousMeta previousArguments : ℕ) (initial : Bool)
local notation "datedInput" pr:arg sc:arg => I₀ previousMeta previousArguments initial pr sc
set_option hygiene false
local notation "u" => datedInput prepared sceneRoom
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
local notation "imageOf" degreeAt:arg capAt:arg => fromNamed_root_image (B:=B) drift degree payload e previous M nextM
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
local notation "occ" x:arg => fun hostIndex groupIndex=>actualBit B B.next.valid.host hostIndex groupIndex x
local notation "scaled" => (⟨quantityDims B 1 HH height₁ (2^e) M,qbits⟩ : DescentResetControlRegisters.Chart)

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
local notation "snapAt" => PaddedSnapshot B input.valid.host (v).middle.rootField

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

open DescentRotorWindowArchive DescentIssuedFallbackPanel DescentPrimitivePalette
local notation "srcRow" bank:arg menu:arg paid:arg => rawAt (pos bank) (hh bank) (band bank) menu paid
local notation "cross" => congrArg (fun size=>DescentRotorWindowArchive.count input.placement.degree size input.placement.cap)
  (congrArg (fun size=>2^(size-(T).commonDepth)) B.keyWidth)
local notation "seenAt" row:arg bank:arg => FreshObservation (p:=p) (field:=rotor) (query:=q₁) (lanes:=M)
  (nodes:=S.retainedNodes) (args:=S.retainedArgumentsAt G drift) B row (.inr bank)
local notation "candidate" => (v).receiver
local notation "rowsAt" dd:arg ready:arg mem:arg cd:arg μ:arg measured:arg dst:arg => DateInputs.OriginalPublicRowsAt (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom dd ready mem cd μ measured dst
local notation "observed" ready:arg dst:arg block:arg size:arg shape:arg rh:arg rg:arg law:arg => DateInputs.ObservedFreshRow (B:=B) drift degree payload e
  previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
  previousMeta previousArguments initial prepared sceneRoom ready dst block size shape rh rg law

set_option hygiene true
set_option maxHeartbeats 1800000
set_option maxRecDepth 6144

include accepted

/-- All six measured tap columns and the occupied badge at this particular gate
come from one issued menu and the predecessor packet selected by the same bank. -/
theorem DateInputs.named_good_observation_of_menu
    (prepared : (rc).PreparedFits book)
    (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (dd:venue.degree=D) (cd:input.placement.cap=cap)
    (gr:z=S.grainAt G.b p (age+1)) (growth:G.b≤2^S.capGain)
    (elapsed:0<age) (sorted:SourceSorted W input.order)
    (shape:config=K) (R:(u).MeasuredChannels (Fintype.card B.next.V)) (dst:Memory w)
    (capture:DateInputs.CaptureRoom R dst) (selfAt:CapturedSelf B (u) R)
    (side:Bool) (root:(Z).placement.Good) (cell:(DescentCommonPalette.rotor (Z).graph).Site)
    (menu:(deck_ (pos (born side root cell))).Values head_ gang_)
    (paid:(deck_ (pos (born side root cell))).casts.bits=(C₀).fallbackBits)
    (packets:rows_ (pos (born side root cell)))
    (issued:menu=(u).issuedPublicValues (pos (born side root cell)) R B.frame.basis rfl rfl rfl rfl rfl rfl
      menu.active menu.register packets)
    (acts:∀h₀ g₀,(menu.active h₀ g₀).val=((scaled).enabled (occ (pos (born side root cell))) (fun _=>1) h₀ g₀).val)
    (regs:∀j h₀ g₀,(menu.register j h₀ g₀).val=((scaled).enabled (occ (pos (born side root cell)))
      (controlScalar B input.valid.host B.next.valid.host j) h₀ g₀).val)
    (positive:0<HH) (snap:snapAt) (groupAt:group₁*2^k=2^(T).commonDepth)
    (ms:DescentRotorWindowArchive.count (config).oldDegree (config).donors (config).oldCap=
      DescentRotorWindowArchive.count input.placement.degree (2^res) input.placement.cap)
    (received:∀(j:DescentRotorWindowArchive.Input (config).oldDegree (config).donors (config).oldCap) (old:input.V),
      (Z).packetOwner T rank positive (hh (born side root cell))=idx old →
      ((config).oldData (srcRow (born side root cell) menu paid) j).val=
      (recordedBoard B snap old ((finProdFinEquiv (band (born side root cell),pos (born side root cell))).cast groupAt)
        (ix.symm (((ix j).cast ms).cast cross))).val) :
    seenAt (Config.relabel shape B.dimension.symm (srcRow (born side root cell) menu paid)) (born side root cell) :=by
  let bank:=born side root cell
  let rawRow:=srcRow bank menu paid
  let row:=Config.relabel shape B.dimension.symm rawRow
  have budget : 0<cap:=Nat.mul_pos
    (Chronology.DonorDate.prefix_cap_pos G.b S.rounds g S.height age G.base_pos) (by decide)
  have ⟨headerActive,capacity,depth_,affirm,rank_,_,layers⟩:=DateInputs.named_bank_good_registers (B:=B) accepted
    drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned
    fitsCut count previousMeta previousArguments initial prepared sceneRoom dd cd gr growth side root cell menu acts regs
  obtain ⟨header,scalar,_,mat⟩:=Config.good_native_row shape B.dimension.symm rawRow
  have ck:((K).reg row 0).val=input.placement.cap:=(scalar 0).trans capacity
  have coordinates:=DateInputs.good_menu_coordinates (B:=B) drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom dd cd shape budget R dst capture selfAt side root cell menu paid packets issued
  have coarse := bank_coarse_block B bank
  have grow : (v).middle.rootField≤rotor:=(Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have small : max (max res (2^(Z).n)) (2^res)<2^(v).middle.rootField:=
    (original_middle_field_room B venue.degree cap Ht).1
  have gather:=good_matrix_gathered (p:=p) (field:=rotor) (query:=q₁) (lanes:=M)
    (nodes:=S.retainedNodes) (args:=S.retainedArgumentsAt G drift) (grain:=p) B (snap.widen grow) positive
    side root cell groupAt row (by
      intro j old whereOld
      let orig:=ix.symm ((ix j).cast ms.symm)
      have addr : (ix j).val=(ix orig).val:=by simp [orig]
      have native:=received orig old whereOld
      simp only [orig,Equiv.apply_symm_apply,Fin.cast_cast,Fin.cast_refl] at native
      exact (mat j orig addr).trans (native.trans (recordedBoard_widen B snap grow small old _ _).symm))
  have rows₀:=reached_good_tap_rows_at (p:=p) (field:=rotor) (query:=q₁) (lanes:=M)
    (nodes:=S.retainedNodes) (args:=S.retainedArgumentsAt G drift) (grain:=p) B accepted elapsed sorted
    (snap.widen grow) (small.trans_le (Nat.pow_le_pow_right (by decide) grow)) side root row gather coordinates.1
    nativeH M rotor (pos bank) (band bank) coarse coordinates.2 ck
  exact ⟨fun zero=>headerActive ((header 0).symm.trans zero),ck,rows₀,(scalar 1).trans depth_,
    congrArg (fun value : ℕ => value % 2) ((scalar 2).trans affirm),layers,(Z).localShape T (hostAt bank),(scalar 3).trans rank_,
    (original_bank_actor B bank).2.2⟩

/-- A reached original good site supplies all observations at the same numeric
slot that the native operand reader addresses. -/
theorem DateInputs.good_observation_at_slot
    (prepared : (rc).PreparedFits book)
    (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (dd:venue.degree=D) (ready:(u).Ready) (mem:Memory w) (cd:input.placement.cap=cap)
    (gr:z=S.grainAt G.b p (age+1)) (μ:DescentGL.Layout (E).dim) (measured dst:Memory w) (atDate:rowsAt dd ready mem cd μ measured dst)
    (growth:G.b≤2^S.capGain) (elapsed:0<age) (sorted:SourceSorted W input.order)
    (block:Fin (candidate).blocks) (size:HH*rows=(C₀).placement.sparse) (shape:config=K)
    (hx:(candidate).blocks=2^k) (aligned:(candidate).hosts=(v).sheets.hosts)
    (groupsAt:(candidate).groups=group₁) (rh:Fin (candidate).hosts) (rg:Fin (candidate).groups)
    (side:Bool) (root:(Z).placement.Good) (cell:(DescentCommonPalette.rotor (Z).graph).Site)
    (home:operandLocation B (block.cast hx) (rh.cast aligned) (rg.cast groupsAt)=
      some (DescentSharedCableNames.Stage.home B.next.placement (bankSite (born side root cell)))) :
    observed ready dst block size shape rh rg (fun row=>seenAt row (born side root cell)) :=by
  let bank:=born side root cell
  obtain ⟨atBlock,atHost,atGroup⟩:=location_coordinates B (block.cast hx) (rh.cast aligned) (rg.cast groupsAt) _ home
  have blockEq : block=pos bank:=Fin.ext (congrArg Fin.val atBlock)
  have hostEq : rh=hh bank:=Fin.ext (congrArg Fin.val atHost)
  have groupEq : rg=band bank:=Fin.ext (congrArg Fin.val atGroup)
  subst block
  subst rh
  subst rg
  have positive : 0<HH:=Nat.zero_lt_of_lt (idx (B.frame.host.symm root.val.1)).isLt
  obtain ⟨R,capture,selfAt,hRaw,sRaw,xCount,all⟩:=DateInputs.fromNamed_public_recorded_matrix_at
    (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil
    fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom dd ready mem cd μ measured dst atDate positive
  obtain ⟨menu,paid,source,acts₀,regs₀,packets,issued,_,_,hdr,xs,rootRead,groupAt,fs,ms,reads⟩:=all (pos bank)
  refine ⟨menu,source,?_⟩
  let I:=imageOf dd cd
  let snap:=root_snapshot B input.valid.host I.receiver I.book I.prepared measured hdr xs
  exact DateInputs.named_good_observation_of_menu (B:=B) accepted drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
    prepared sceneRoom dd cd gr growth elapsed sorted shape R dst capture selfAt side root cell menu paid packets issued
    acts₀ regs₀ positive snap groupAt ms (fun j=>((reads (hh bank) (band bank)).2 j).2)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
