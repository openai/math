import OAI.Hierarchy.DescentNamedPrimaryEmptyShape
import OAI.Hierarchy.DescentMeasuredBankBadge

namespace OAI
/-! # Exhaustive physical roles of an occupied successor site, including empty gate lists -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentStageEdgeReceipt DescentCompiler
open scoped Classical
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset cap ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation:max "installed" field:arg => B.reblock.destination (((Z).resetNames T).symm field)

/-- Every occupied physical site originated at one primary, one relay, or one bank site. -/
theorem reblocked_site_cases (v : B.reblock.result.graph.Site) :
    (∃t,v=installed (.inl (false,t))) ∨ (∃t,v=installed (.inl (true,t))) ∨
    ∃s,v=installed (.inr s) :=by
  obtain ⟨old,rfl⟩ := DescentPaidResidentCount.destination_onto B.reblock v
  have recover (j) (tag : (Z).resetNames T old=j) : B.reblock.destination old=installed j :=
    congrArg B.reblock.destination ((((Z).resetNames T).symm_apply_apply old).symm.trans
      (congrArg ((Z).resetNames T).symm tag))
  rcases tag : (Z).resetNames T old with ⟨s,t⟩ | bank
  · cases s with
    | false => exact Or.inl ⟨t,recover _ tag⟩
    | true => exact Or.inr (Or.inl ⟨t,recover _ tag⟩)
  · exact Or.inr (Or.inr ⟨bank,recover _ tag⟩)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

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
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
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

open DescentSortedRoster
open DescentSixParty.ClosedReset.Window DescentOperandRootPull DescentSixParty.PackedFlow.Channels
local notation "setup" => (v).setup

open DescentSixParty.Chronology DescentSixParty.Chronology.DatePorts DescentBundleHistory
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

open DescentPaidResidentCount
local notation:max "installed" field:arg => B.reblock.destination (((Z).resetNames T).symm field)

open private paired_name equal_target_height from OAI.Hierarchy.DescentNamedPrimaryEmptyShape

set_option maxRecDepth 4096 in
set_option maxHeartbeats 700000 in
include degreeAt in
/-- Occupation identifies the compact host even if there is no operator at the
requested ordinal. Only primary trunks select the retained operand table. -/
theorem DateInputs.occupied_role_cases (site : B.reblock.result.graph.Site)
    (used : occupies B.next.placement (Equiv.refl _) B.next.vertex ⟨rack.val,present⟩
      (group.cast places.groups.symm) (block.cast (congrArg (2^·) places.radix.symm)) site) :
    (u).menu.keep tok=true ∨ (∃t,site=installed (.inl (true,t))) ∨ ∃bankSite,site=installed (.inr bankSite) :=by
  rcases reblocked_site_cases B site with ⟨t,rfl⟩|other
  · left
    let actor:=(B.next.placement.pos (installed (.inl (false,t)))).2
    let hostFields₀:=(Z).hostFields T rank actor
    have hostAt : (B.next.vertex actor).val=rack.val:=congrArg Fin.val used.1
    have ordered:(⟨rack.val,present⟩:Fin (Fintype.card B.next.V))=(Z).denseHostRank T rank actor:=
      Fin.ext (hostAt.symm.trans (dense_physical B input.valid.host actor).symm)
    let same:rows=(setup).placement.shapes:=B.public_hub_slots.trans (by
      change (roster board k height_).card=(roster board k (GroupStage.depthBound venue.degree n f g)).card
      rw [degreeAt])
    have looked : dirs ⟨rack.val,present⟩=finProdFinEquiv (hostFields₀.1,hostFields₀.2.cast same):=by
      change ((Z).rawAtIndex T rank _).cast size=_
      rw [ordered]
      exact (congrArg (Fin.cast size) ((Z).rawAtIndex_at T rank actor)).trans (paired_name rfl same size _ _)
    have shape_:tok=hostFields₀.2.cast same:=by
      simp only [looked,DescentResetRetainedPlacement.Chart.shape]
      exact congrArg Prod.snd (finProdFinEquiv.symm_apply_apply _)
    have target:(u).menu.target tok=DescentResetActorClass.primaryTarget (Z).graph res_ actor.val:=by
      rw [shape_,(u).menu.target_book]
      have measured:=calendar_primary_target B input.valid.host actor
      change DescentResetActorClass.targetBook board k (GroupStage.depthBound venue.degree n f g) _=_
      exact (equal_target_height board k (congrArg (fun deg₀ => GroupStage.depthBound deg₀ n f g) degreeAt) _ _ rfl).trans measured
    have placed:actor=(Z).placed T (((Z).resetNames T).symm (.inl (false,t))):=
      congrArg (fun cell=>cell.1.2) (named_home B (((Z).resetNames T).symm (.inl (false,t))))
    apply (u).menu.keep_of_target tok (code t)
    rw [target,placed]
    let view := DescentCommonHost.bankNode (Z).placement (Z).graph (T).commonDepth (T).code (Z).positive (Z).pay (Z).circuit d
    let read : (Bool×(Z).Fallback) ⊕ (Z).bank.Site → _ := Sum.elim
      (fun st => DescentCommonHost.Node.trunk st.1 (shortName (T).commonDepth ((T).code st.2))) view
    exact congrArg (fun j => DescentResetActorClass.primaryTarget (Z).graph res_ (read j))
      (((Z).resetNames T).apply_symm_apply (.inl (false,t)))
  · exact Or.inr other
end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
