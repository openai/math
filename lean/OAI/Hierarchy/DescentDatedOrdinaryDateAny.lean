import OAI.Hierarchy.DescentDatedPublicOrdinaryCode
import OAI.Hierarchy.DescentPublicDonorAny
import OAI.Hierarchy.DescentPublicMeterAny
import OAI.Hierarchy.DescentDatedOrdinaryFrame

namespace OAI
/-! # The complete ordinary date on an arbitrary original ballot -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup DescentPackedProfileInstall
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (root shelf header : ℕ)
    (input : Dated.Operands) (count : Bank) (wires : v.signed.Input) (B : StageVenueTail.Sources)
    {w : ℕ} (s : ResultSteps w) (bank : v.ResultRoom (v.stageStart root) B w)
    (d : DonorDate) (positive : 0< d.exponent)
local notation "floor" => v.stageStart root
local notation "a" => d.schedule v.payload v.seats v.bitsPerField
local notation "rot" => (a).rotationEnd input.roster floor
local notation "rom" => (a).prepareAt input.roster floor
local notation "src" => sourceBank shelf v.profileRepack.seats v.profileRepack.oldLanes
local notation "dst" => (v.area.matcher v.old floor).raw
local notation "load" => v.archivePhase root shelf w
local notation "meter" => d.counter v.payload rot header
local notation "oldBanks" => d.matcherOutput v.payload v.seats input rom
local notation "dep" => d.afterMatcher v.payload v.seats input v.bitsPerField floor w
local notation "measure" => (⟨v.prior.placement.wire,v.prior.placement.z,v.prior.placement.hist⟩:Dated.Measures)
local notation "stored" => v.date root shelf header input count wires B s bank d positive
local notation "before" => v.beforeCount floor input count wires B s bank
local notation "close_" => v.finish floor input count wires B s bank

structure Room : Prop where
  source : (src).Fits w root
  raw : (dst).base+(dst).size< 2^w
  matcher : (a).Space input w floor
  donor : d.PhaseRoom v.payload rot w oldBanks
  late : v.ResultRuns floor input count wires s
  topology : (v.area.matcher v.old floor).layout.topology.Fits w (v.primitiveEnd floor)
  limit : v.fullEnd root< 2^w
  counter : (meter).Room w

variable (fit : Room v root shelf header input count wires s d)
local notation "matcher" => (a).nativePhase v.gadget positive input measure w floor fit.matcher

def dateOutput (m : Memory w) :=(meter).image ((close_).image ((dep).image ((matcher).image ((load).image m))))

theorem date_any (m : Memory w) :
    (stored).Runs m (v.dateOutput root shelf header input count wires B s bank d positive fit m) ∧ (stored).cheap :=by
  let initial:=(load).image m
  let chosen:=(matcher).image initial
  let assessed:=(dep).image chosen
  have booted : (load).Runs m:=v.archivePhase_runs root shelf w m fit.source (v.archive_geometry root).1 fit.raw
  have selected : (matcher).Runs initial:=(a).nativePhase_all v.gadget positive input measure w floor fit.matcher initial
  have debited : (dep).Runs chosen :=(d.afterMatcher_any v.payload v.seats input v.bitsPerField floor w chosen fit.donor).1
  have gathered : (close_).Runs assessed:=
    (before).seq_runs (v.counter floor w) assessed ((v.before_span floor input count wires B s bank fit.late).2 _).1
      (v.counter_run floor _ fit.topology fit.limit).1
  constructor
  · refine ⟨(close_).image assessed,?_,?_⟩
    · intro P R K machine
      exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then booted selected) debited) gathered machine
    · exact (meter).counter_any _ fit.counter
  · let main := (((load).seq matcher).seq dep).seq close_
    change ProtocolRAM.CheapCode main.program ∧ ProtocolRAM.CheapCode ((meter).program w)
    exact ⟨@NativePhase.cheap w main, @Dated.Meter.counter_cheap meter w⟩

/-- The accepted matcher and its donor publication retain the initial private header. -/
theorem donor_input_low (m : Memory w) (j : ℕ) (low : j<root) (start : root≤rot) :
    (dep).image ((matcher).image ((load).image m)) j=m j :=by
  have fromRoot : root≤floor:=by
    change root≤v.profileRepack.endAddress root
    rw [v.profileRepack.translate]
    omega
  have installed:=v.archivePhase_frame root shelf w m fit.source (v.archive_geometry root).1 fit.raw j
    (.inl low) (.inl (low.trans_le (fromRoot.trans (v.archive_geometry root).1)))
  have matched:=(a).any_frame input w floor v.gadget positive measure fit.matcher ((load).image m) j
    (.inl (low.trans_le fromRoot))
  have donor:=(d.afterMatcher_any v.payload v.seats input v.bitsPerField floor w ((matcher).image ((load).image m)) fit.donor).2 j
    (.inl (low.trans_le start))
  exact donor.trans (matched.trans installed)

include fit in
/-- The successor construction preserves all original donor rows until the private meter runs. -/
theorem meter_input_low (m : Memory w) (j : ℕ) (low : j<v.donorEnd floor) :
    (close_).image m j=m j :=by
  have span:=v.before_span floor input count wires B s bank fit.late
  have held:=(span.2 m).2 j (.inl low)
  have counted:=(v.counter_run floor ((before).image m) fit.topology fit.limit).2 j (.inl (low.trans_le span.1))
  exact counted.trans held

/-- The public emitter preserves every previous observation except its private
count accumulator. This holds on every proposal, including after rejection. -/
theorem date_low (m : Memory w) (j : ℕ) (hj : j< root) (other : j≠header)
    (order : root≤ rot ∧ rot≤ (meter).base ∧ root≤ v.donorEnd floor) :
    v.dateOutput root shelf header input count wires B s bank d positive fit m j=m j :=by
  let initial:=(load).image m
  let chosen:=(matcher).image initial
  let assessed:=(dep).image chosen
  have fromRoot : root≤ floor:=by change root≤ v.profileRepack.endAddress root;rw [v.profileRepack.translate];omega
  have installed:=v.archivePhase_frame root shelf w m fit.source (v.archive_geometry root).1 fit.raw j
    (.inl hj) (.inl (hj.trans_le (fromRoot.trans (v.archive_geometry root).1)))
  have matched:=(a).any_frame input w floor v.gadget positive measure fit.matcher initial j (.inl (hj.trans_le fromRoot))
  have donor:=(d.afterMatcher_any v.payload v.seats input v.bitsPerField floor w chosen fit.donor).2 j
    (.inl (hj.trans_le order.1))
  have span:=v.before_span floor input count wires B s bank fit.late
  have held:=(span.2 assessed).2 j (.inl (hj.trans_le order.2.2))
  have counted:=(v.counter_run floor ((before).image assessed) fit.topology fit.limit).2 j
    (.inl (hj.trans_le (order.2.2.trans span.1)))
  have last:=(meter).counter_frame ((close_).image assessed) fit.counter j other
    (.inl (hj.le.trans (order.1.trans order.2.1)))
  exact last.trans (counted.trans (held.trans (donor.trans (matched.trans installed))))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
