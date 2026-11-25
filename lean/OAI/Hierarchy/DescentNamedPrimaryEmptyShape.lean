import OAI.Hierarchy.DescentNamedPrimaryPacketRows
import OAI.Hierarchy.DescentRegisteredPrimaryVacancy

namespace OAI
/-! # Reading the compact primary name when the archived local node is absent -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty.Chronology DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
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
  (venue : StageVenueTail.Date) (io : Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "namedSuccessor" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤wide-k) (fitsSigned : e≤previous) (fitsCut : previous≤cc) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "early" => (namedSuccessor).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (namedSuccessor).front.SceneRoom early ((namedSuccessor).issuedScene base₀ older) w)
local notation "dateInput" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx
local notation "HH" => S.hostSize age

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage

local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (roster (Z).graph res (GroupStage.depthBound D n f g)).card

open DescentSortedRoster
open DescentSixParty.ClosedReset.Window DescentOperandRootPull DescentSixParty.PackedFlow.Channels
local notation "setup" => (namedSuccessor).setup

open DescentSixParty.Chronology.DatePorts
open DescentLocalArchiveOrder DescentKernelHistory DescentPrimitivePalette DescentRetainedRangeDigits
open DescentFallbackShapeTable DescentRelativeContacts DescentIssuedFallbackPanel
variable (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
variable (oldA : Archive W) (num : Local oldA.bit) (hp : 0<p) (whole : p∣(Z).unit)
local notation "after_" => (resetArchive B p hp whole oldA).bit
local notation "newNum" => DescentLocalArchiveOrder.reset B p hp whole oldA num
variable (ports : DatePorts) (places : DatePorts.RangeRoom ports B.next after_)
    (block : Fin (2^ports.venue.k)) (node : Fin ports.nodes) (rack : Fin ports.operandHosts) (group : Fin ports.venue.groups)
variable (present:rack.val<Fintype.card B.next.V)
    (absent:DatePorts.slotAt ports B.next after_ newNum places block node rack group=none)
    (size:HH*rows=(setup).placement.sparse)
local notation "dirs" => fun j:Fin (Fintype.card B.next.V)=>((Z).rawAtIndex T rank j).cast size
local notation "tok" => (setup).placement.shape (dirs ⟨rack.val,present⟩)
local notation:max "oldHost" t:arg => B.frame.host.symm ((T).code t).1
local notation "res_" => (Z).k-(T).commonDepth
local notation:max "code" t:arg => DescentFallbackShapeTable.cell res_ (shortName (T).commonDepth ((T).code t)).2
local notation:max "hi" t:arg => (Z).rootBlock T (.inr t)
local notation "out" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "high_" => (out).symm (group.cast places.groups.symm,block.cast (congrArg (2^·) places.radix.symm))
local notation:max "available" t₀:arg t:arg => ((T).code t).1=B.frame.host (oldHost t₀) ∧ hi t=high_ ∧ code t=code t₀
local notation "height_" => GroupStage.depthBound D n f g

private theorem paired_name {H Q H' Q':ℕ} (host:H=H') (num:Q=Q') (size:H*Q=H'*Q')
    (v:Fin H) (j:Fin Q) : (finProdFinEquiv (v,j)).cast size=finProdFinEquiv (v.cast host,j.cast num):=by
  subst H';subst Q';rfl

private theorem equal_target_height {dim deg : ℕ} (graph : NonlinearExpanders.Graph dim deg)
    (residual : ℕ) {height₀ height₁ : ℕ} (sameHeight : height₀ = height₁)
    (i₀ : Fin (roster graph residual height₀).card) (i₁ : Fin (roster graph residual height₁).card)
    (sameIndex : i₀.val = i₁.val) :
    DescentResetActorClass.targetBook graph residual height₀ i₀ =
      DescentResetActorClass.targetBook graph residual height₁ i₁ := by
  subst height₁
  exact congrArg _ (Fin.ext sameIndex)

set_option maxHeartbeats 850000 in
include absent degreeAt in
theorem DateInputs.named_empty_primary_shape (retained:(dateInput).menu.keep tok=true) :
    ∃t₀:(Z).Fallback,(dateInput).bank.which tok=some (code t₀) ∧
      ((setup).placement.previous (dirs ⟨rack.val,present⟩)).val=(idx (oldHost t₀)).val ∧
      ((∃t:(Z).Fallback,available t₀ t ∧
         (∑u:DescentNamedContact.Fibre (T).home t,Fintype.card (oldA.bit.recipe u.val).Node)≤node.val) ∨
       ¬∃t:(Z).Fallback,available t₀ t):=by
  let actor:=(DescentStageEdgeReceipt.dense B.next.vertex).symm ⟨rack.val,present⟩
  let hostFields:=(Z).hostFields T rank actor
  have dense:(B.next.vertex actor).val=rack.val:=congrArg Fin.val
    ((DescentStageEdgeReceipt.dense B.next.vertex).apply_symm_apply ⟨rack.val,present⟩)
  have ordered:(⟨rack.val,present⟩:Fin (Fintype.card B.next.V))=(Z).denseHostRank T rank actor:=by
    exact Fin.ext (dense.symm.trans (dense_physical B input.valid.host actor).symm)
  let same:rows=(setup).placement.shapes:=B.public_hub_slots.trans (by
    change (roster board k height_).card=(roster board k (GroupStage.depthBound venue.degree n f g)).card
    rw [degreeAt])
  have looked : dirs ⟨rack.val,present⟩=finProdFinEquiv (hostFields.1,hostFields.2.cast same):=by
    change ((Z).rawAtIndex T rank _).cast size=_
    rw [ordered]
    exact (congrArg (Fin.cast size) ((Z).rawAtIndex_at T rank actor)).trans (paired_name rfl same size _ _)
  have shape_:tok=hostFields.2.cast same:=by
    simp only [looked,DescentResetRetainedPlacement.Chart.shape]
    exact congrArg Prod.snd (finProdFinEquiv.symm_apply_apply _)
  have oldHost_:((setup).placement.previous (dirs ⟨rack.val,present⟩))=hostFields.1:=by
    simp only [looked,DescentResetRetainedPlacement.Chart.previous]
    exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply _)
  have target:(dateInput).menu.target tok=DescentResetActorClass.primaryTarget (Z).graph res_ actor.val:=by
    rw [shape_,(dateInput).menu.target_book]
    have measured:=calendar_primary_target B input.valid.host actor
    change DescentResetActorClass.targetBook board k (GroupStage.depthBound venue.degree n f g) _=_
    exact (equal_target_height board k (congrArg (fun d => GroupStage.depthBound d n f g) degreeAt) _ _ rfl).trans measured
  have existsKey:∃k₀,(dateInput).menu.target tok=some k₀:=by
    unfold OperandMenu.keep at retained
    unfold OperandMenu.target
    split at retained <;> simp_all
  obtain ⟨key,keyAt⟩:=existsKey
  obtain ⟨t₀,atActor,codeEq,cases_⟩:=registered_primary_empty_cases B hp whole oldA num ports places block node
    rack group present absent (target.symm.trans keyAt)
  refine ⟨t₀,keyAt.trans (congrArg some codeEq.symm),?_,cases_⟩
  rw [oldHost_]
  change (rank (DescentDenseHostOrder.position (Z).graph actor.val)).val=_
  rw [show actor=(Z).placed T (((Z).resetNames T).symm (.inl (false,t₀))) from atActor,
    placed_reset_actor_value]
  rfl

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
