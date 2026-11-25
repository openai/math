import OAI.Hierarchy.DescentOrdinaryObservedOutput
import OAI.Hierarchy.DescentDatedObservedProfile
import OAI.Hierarchy.DescentPhysicalDateHistory

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch.Local.Stage DescentPacking.PackedMatch DescentSIMDLookup DescentPackedProfileInstall
open DescentPackedProfileWide DescentTerminalEpochDecoder DescentTerminalEpochChart DescentGroupPeerOrder DescentStageEdgeReceipt
open DescentColonies DescentKernelHistory.BitDescription DescentCompiler DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (input : Dated.Operands) (root shelf header : ℕ)
  (count : Bank) (wires : v.signed.Input) (B : StageVenueTail.Sources) {w : ℕ} (s : ResultSteps w)
  (bank : v.ResultRoom (v.stageStart root) B w) (d : DonorDate) (positive : 0< d.exponent)
local notation "floor" => v.stageStart root
local notation "A" => v.prior.placement
local notation "a" => d.schedule v.payload v.seats v.bitsPerField
local notation "real_" => v.area
local notation "rot" => (a).rotationEnd input.roster floor
local notation "saved" => (real_).flagEnd input.roster floor+2^v.k
local notation "ptr" => v.primitiveEnd floor
local notation "load" => v.archivePhase root shelf w
local notation "dep" => d.afterMatcher v.payload v.seats input v.bitsPerField floor w
local notation "late" => v.beforeCount floor input count wires B s bank
local notation "meter" => d.counter v.payload rot header
local notation "measure" => (⟨(A).wire,(A).z,(A).hist⟩:Dated.Measures)
variable (fit : Room v root shelf header input count wires s d)
variable (wide : Fintype.card v.prior.V≤ 2^v.level)
local notation "names" => GroupStage.plane v.hostNumbers wide
local notation "rank" => groupRank ((Equiv.refl (Fin (v.schedule.groupCount v.age))).toEmbedding.trans Fin.valEmbedding)
  ((names).trans Fin.valEmbedding)
local notation "μ" => multiplier (A).fieldBits (scannedRows v.nonnegative (A).stage).μ
local notation "roof" => v.donorEnd floor
local notation "publicMatch" => (a).nativePhase v.gadget positive input measure w floor fit.matcher

include fit in
theorem ordinary_history_observations {Pin : Type} (entry : Source Pin) (z : Pin→Bool)
    (choice : ((A).stage.result v.nonnegative).Choice)
    (ext : DescentTerminalEpochBits.width entry.C≤ (real_).shapeAt.digit) (dates : ℕ→DateCode w) (initial : Memory w)
    (same : dates v.age=v.date root shelf header input count wires B s bank d positive)
    (m : Memory w)
    (present : m=DateCode.history dates initial v.age)
    (seen : v.reachedReport input floor wide ((load).image m) choice entry z ext)
    (named : (A).SiteNamed rank) (shapes : a=real_) (roster : v.old=input.roster)
    (forward : rot≤ roof) (afterDonor : d.meterBase v.payload rot+1+d.hosts*chunks d.groups (lanes v.payload d.amount)≤ roof)
    (privateEnd : (meter).endAddr≤ roof) (privateBase : rot≤ (meter).base)
    (apart₁ : v.countAddr root≠header) (apart₂ : saved≠header) :
    DateCode.history dates initial (v.age+1) (v.countAddr root)=(selectionCount v.gadget v.ticket.selection:Word w) ∧
      DateCode.history dates initial (v.age+1) saved=((DescentExterior.matrixCode μ).val:Word w) :=by
  subst m
  apply DateCode.history_event dates initial v.age (Q:=fun out=>
    out (v.countAddr root)=(selectionCount v.gadget v.ticket.selection:Word w) ∧
      out saved=((DescentExterior.matrixCode μ).val:Word w))
  refine ⟨v.dateOutput root shelf header input count wires B s bank d positive fit (DateCode.history dates initial v.age), ?_, ?_⟩
  · rw [same]
    exact (v.date_any root shelf header input count wires B s bank d positive fit _).1
  · have observed:=v.date_count_rotation input root shelf header count wires B s bank d positive fit wide
      entry z choice ext _ seen named shapes roster forward afterDonor privateEnd privateBase apart₁ apart₂
    rw [v.ticket.counted_selection]
    exact observed

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
