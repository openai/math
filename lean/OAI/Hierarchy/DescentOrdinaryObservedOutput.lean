import OAI.Hierarchy.DescentDatedOrdinaryDateAny
import OAI.Hierarchy.DescentDatedObservedWords

namespace OAI
/-! # Pair counts and rotations on the actual final ordinary memory -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch.Local.Stage DescentPacking.PackedMatch DescentSIMDLookup DescentPackedProfileInstall
open DescentPackedProfileWide DescentTerminalEpochDecoder DescentTerminalEpochChart DescentGroupPeerOrder DescentStageEdgeReceipt
open DescentColonies DescentKernelHistory.BitDescription DescentCompiler DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option maxHeartbeats 1000000
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

theorem date_count_rotation {Pin : Type} (entry : Source Pin) (z : Pin→Bool)
    (choice : ((A).stage.result v.nonnegative).Choice)
    (ext : DescentTerminalEpochBits.width entry.C≤ (real_).shapeAt.digit) (m : Memory w)
    (seen : v.reachedReport input floor wide ((load).image m) choice entry z ext)
    (named : (A).SiteNamed rank) (shapes : a=real_) (roster : v.old=input.roster)
    (forward : rot≤ roof) (afterDonor : d.meterBase v.payload rot+1+d.hosts*chunks d.groups (lanes v.payload d.amount)≤ roof)
    (privateEnd : (meter).endAddr≤ roof) (privateBase : rot≤ (meter).base)
    (apart₁ : v.countAddr root≠header) (apart₂ : saved≠header) :
    let final:=v.dateOutput root shelf header input count wires B s bank d positive fit m
    final (v.countAddr root)=((Fintype.card (scannedRows v.nonnegative (A).stage).pairs):Word w) ∧
      final saved=((DescentExterior.matrixCode μ).val:Word w) :=by
  intro final
  let start:=(load).image m
  have fit₁ : (real_).Space input w floor:=shapes ▸ fit.matcher
  let authentic:=(real_).nativePhase v.gadget (A).fieldBits input measure w floor fit₁
  have outcome : (publicMatch).image start=authentic.image start :=by
    have run : (publicMatch).Runs start :=(a).nativePhase_all v.gadget positive input measure w floor fit.matcher start
    have real : authentic.Runs start := (real_).nativePhase_all v.gadget (A).fieldBits input measure w floor fit₁ start
    apply ProtocolRAM.exec_unique (n:=(publicMatch).ticks) (k:=authentic.ticks) authentic.program start _ _ _ real
    have transport {area₁ area₂ : Dated.Ordinary} (eqn : area₁ = area₂)
        (h₁ : 0<area₁.k) (h₂ : 0<area₂.k) :
        area₁.program v.gadget h₁ input measure w floor = area₂.program v.gadget h₂ input measure w floor := by
      subst area₂
      rfl
    rw [←show (publicMatch).program = authentic.program from transport shapes positive (A).fieldBits]
    exact @run
  have sp:=v.before_span floor input count wires B s bank fit.late
  have eqRot : (real_).rotationEnd input.roster floor=rot:=congrArg (fun arena : Dated.Ordinary => arena.rotationEnd input.roster floor) shapes.symm
  have frame (o : Memory w) (j : ℕ) (out : j< (real_).rotationEnd input.roster floor ∨ ptr≤ j) :
      ((dep).seq late).image o j=o j :=by
    rw [eqRot] at out
    have raw:=(d.afterMatcher_any v.payload v.seats input v.bitsPerField floor w o fit.donor).2 j
      (out.imp_right (fun h=>afterDonor.trans (sp.1.trans h)))
    change (late).image ((dep).image o) j = o j
    have under : j < roof ∨ ptr ≤ j := out.imp_left (fun h => h.trans_le forward)
    exact ((sp.2 ((dep).image o)).2 j under).trans raw
  have words:=v.observed_words_at_primitive_end input root wide start choice entry z ext fit₁ roster seen named dep late
    (fun o=>(d.afterMatcher_any v.payload v.seats input v.bitsPerField floor w o fit.donor).1)
    (fun o=>(sp.2 o).1) frame (eqRot.trans_le (forward.trans sp.1)) fit.limit
  have countRoom : ptr≤ v.countAddr root:=by
    change ptr ≤ ptr + 2^v.countBits + v.area.batch
    exact (Nat.le_add_right _ (2^v.countBits)).trans (Nat.le_add_right _ _)
  have matrixRoom : saved≤ rot:=by
    rw [←eqRot]
    change _≤ (real_).flagEnd input.roster floor+2^v.k+1
    exact Nat.le_succ _
  let mid:=(v.finish floor input count wires B s bank).image ((dep).image ((publicMatch).image start))
  have countAt:= (meter).counter_frame mid fit.counter _ apart₁ (.inr (privateEnd.trans (sp.1.trans countRoom)))
  have savedAt:= (meter).counter_frame mid fit.counter _ apart₂ (.inl (matrixRoom.trans privateBase))
  constructor
  · apply countAt.trans
    dsimp only [mid,finish,NativePhase.seq]
    rw [outcome]
    exact words.2.1
  · apply savedAt.trans
    dsimp only [mid,finish,NativePhase.seq]
    rw [outcome]
    exact words.2.2
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
