import OAI.Computability.VPVNP.PairTraversalControllerRunReads
import OAI.Computability.VPVNP.PairTraversalControllerSetupReads
import OAI.Computability.VPVNP.PairTraversalReferenceReads
import OAI.Computability.VPVNP.PairTraversalControllerLocation
import OAI.Computability.VPVNP.PairTraversalReferenceFootprint
import OAI.Computability.VPVNP.PairArenaBudget
import OAI.Computability.VPVNP.CompressorOrdinalProgress

/-!
# Native traversal-controller execution on the selected compression branch

The terminal header points to the completed placement directories. These
physical inputs suffice for one fixed native controller to write the whole
arena, preserve the shared-bit interval, and accept on a unique tape.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalController

open BurstRAM Compression CompressorRecords LocalHistory TraversalRows DirectoryRun
open TraversalRoles TraversalControllerInputs
open scoped Fin.CommRing

variable {w : ℕ}

/-- All controller bursts, including the largest fiber scan, fit this bound. -/
def callFuel (cap : ℕ) : ℕ := setupLen + 7 + (7 * cap + 25)

private theorem tags_info (offset cap base : ℕ) (ls : List TaggedLayer) :
    (tagJobs w offset cap base ls).map Pass.count = ls.map (fun l => l.layer.count) ∧
      ∀ t ∈ tagJobs w offset cap base ls, t.clock = 12 := by
  induction ls generalizing base with
  | nil => exact ⟨rfl, by simp [tagJobs]⟩
  | cons l ls ih =>
    obtain ⟨counts, clocks⟩ := ih (endPos cap base l.layer)
    refine ⟨congrArg (List.cons l.layer.count) counts, ?_⟩
    intro t ht
    exact (List.mem_cons.mp ht).elim (fun h => h ▸ rfl) (clocks t)

private theorem fibers_info (cap previous base : ℕ) (ls : List (Fiber w)) :
    (fiberWorkers cap previous base ls).map (Pass.count ∘ rowJob) =
      ls.map (fun l => l.1.layer.count) ∧
      ∀ t ∈ fiberWorkers cap previous base ls, (rowJob t).clock = 7 * cap + 25 := by
  induction ls generalizing previous base with
  | nil => exact ⟨rfl, by simp [fiberWorkers]⟩
  | cons l ls ih =>
    obtain ⟨counts, clocks⟩ := ih base (endPos cap base l.1.layer)
    refine ⟨congrArg (List.cons l.1.layer.count) counts, ?_⟩
    intro t ht
    exact (List.mem_cons.mp ht).elim (fun h => h ▸ rfl) (clocks t)

variable {k A : Type*} [Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f) {n : ℕ} (T : ℕ)
variable (hT : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
variable (z : (B.execute f hf T hT X).Choices) (base : ℕ) (raw : Memory w)
variable (ds : let vs := executeLevels B f hf T hT X z
  (i : Fin vs.length) → LevelDirectory vs[i] raw base)

private theorem selected_jobs_info :
    let tags := selected B f hf T hT X z
    let rows := selectedJobs B f hf T hT X z base raw ds
    (rows.map (Pass.count ∘ rowJob)) = tags.map (fun l => l.layer.count) ∧
      ∀ t ∈ rows, (rowJob t).clock ≤ 7 * B.recordLimit + 25 := by
  let cap := B.recordLimit
  let ls := levelFibers (executeLevels B f hf T hT X z) ds
  let old := leafLayer (siteOrder X)
  obtain ⟨counts, clocks⟩ := fibers_info cap base (endPos cap base old) ls
  rw [selectedJobs_eq]
  constructor
  · change old.count :: (fiberWorkers cap base (endPos cap base old) ls).map _ = _
    rw [counts]
    have h := congrArg (List.map (fun l : TaggedLayer => l.layer.count)) (levelFibers_tags _ ds)
    exact congrArg (List.cons old.count) (by simpa only [List.map_map, Function.comp_def] using h)
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | h
    · change 14 ≤ 7 * cap + 25; omega
    · exact (clocks t h).le

open private probes_le from OAI.Computability.VPVNP.PairArenaBudget

/-- The selected raw scans and resident header instantiate the complete native
controller. Its charges include both resets at every level and the sentinel. -/
theorem selected_run_with_reads (pub : Fin 11 → Word w) (F H first pitch : ℕ)
    (d : Resident pub raw H first pitch (words B.recordLimit (selectedLayers B f hf T hT X z) + F)
      B.recordLimit base ⟨leafLayer (siteOrder X), .cursor⟩
      (levelFibers (executeLevels B f hf T hT X z) ds))
    (headersBefore : ∀ j ≤ (executeLevels B f hf T hT X z).length, first + j * pitch + 28 ≤ base)
    (belowHeader : base + 2 * words B.recordLimit (selectedLayers B f hf T hT X z) + F ≤ H)
    (ordinalFit : 2 * (selected B f hf T hT X z).length * (X.positions + 1) < 2 ^ w) :
    let cap := B.recordLimit
    let ls := selectedLayers B f hf T hT X z
    let size := words cap ls
    let off := size + F
    let tags := selected B f hf T hT X z
    let rowJobs := selectedJobs B f hf T hT X z base raw ds
    let calls := 2 * (ls.map Layer.count).sum + 2 * tags.length + 1
    let arena := build cap base base ls (writeTags off cap base tags raw)
    let program := (Native.machine pub).program
    ∃ ts rs out, RolePasses off cap base tags raw ts ∧
      DirectoryRun.Segments rowJobs (after raw (eventLog ts)) rs ∧
      Segment program (callFuel cap) (some 0) none raw arena calls
        (257 * calls + countProbes (eventLog (ts ++ rs))) out ∧
      RAMBuckets.cost Report.probes out ≤ (2 * cap + 1294) *
        (((S.steps + 1) * T + 1) * X.positions) ∧
      (∀ r ∈ out, r.probes ≤ r.events.length ∧ r.events.length < callFuel cap) ∧
      Reads w (after raw (eventLog out)) off cap base tags ∧
      AllRows w (after raw (eventLog out)) cap base base ls ∧
      (∀ x < base, after raw (eventLog out) x = raw x) ∧
      (∀ i < F, after raw (eventLog out) (base + size + i) = raw (base + size + i)) ∧
      SourceTransport.Reads (TerminalLink.workerCell (TerminalLink.header pub)) (eventLog out) ∧
      ∀ (bits : List (List Bool)) (other : List (Report w)),
        runSegment program (callFuel cap) (some 0) raw bits = some other →
        endState (some 0) other = none → bits = List.replicate calls [] ∧ other = out := by
  intro cap ls size off tags rowJobs calls arena program
  let jobs := tagJobs w off cap base tags ++ rowJobs.map rowJob
  let visits := ((S.steps+1)*T+1) * X.positions
  change base + 2 * size + F ≤ H at belowHeader
  have hh : H < 2^w := by have := d.headerFits; omega
  have fit : base + 2 * size + F < 2 ^ w := belowHeader.trans_lt hh
  obtain ⟨ts, rs, ht, hr, image, tagsOK, rowsOK, bitsOK, refCalls, refProbes⟩ :=
    native_arena B f hf T hT X z base F raw ds fit
  have typed : Reference jobs raw (ts ++ rs) := Reference.of_passes ht hr
  have layers : tags.map TaggedLayer.layer = ls := selected_layers B f hf T hT X z
  have hsize : tagWords cap tags = size := congrArg (words cap) layers
  have below : off + base + tagWords cap tags ≤ H := by rw [hsize]; dsimp only [off]; omega
  have headers := selected_reference_schedule B f hf T hT X z base raw ds d headersBefore
    ts rs ht hr below
  have schedule : Schedule pub raw off cap base tags rowJobs := (headers 0 (Nat.zero_le _)).1
  have phases : jobs.length = 2 * tags.length := by simp [jobs, schedule.jobs_length, two_mul]
  have positive : 0 < tags.length := Nat.succ_pos _
  have capCount (j : Fin jobs.length) : jobs[j].count ≤ X.positions := by
    let layer : Fin tags.length := ⟨j.val % tags.length, Nat.mod_lt _ positive⟩
    have hc := (schedule.lookup layer).1
    rw [show jobs[j].count = _ from schedule.pass_count j, hc]
    apply selected_layer_count_le B f hf T hT X z
    change tags[layer].layer ∈ ls
    rw [← layers]
    exact List.mem_map_of_mem (List.getElem_mem layer.isLt)
  obtain ⟨tagCounts, tagClock⟩ := tags_info (w := w) off cap base tags
  obtain ⟨rowCounts, rowClock⟩ := selected_jobs_info B f hf T hT X z base raw ds
  have clock (j : Fin jobs.length) : setupLen + 7 + jobs[j].clock ≤ callFuel cap := by
    apply Nat.add_le_add_left
    have hj := List.getElem_mem (l := jobs) j.isLt
    rcases List.mem_append.mp hj with h | h
    · exact (tagClock _ h).trans_le (by omega)
    · obtain ⟨row, hw, he⟩ := List.mem_map.mp h
      exact he ▸ rowClock row hw
  have stable : AtPrefixes (RunInputs pub tags.length X.positions jobs) raw (ts ++ rs) := by
    intro q hq
    obtain ⟨sched, site⟩ := headers q hq
    exact ⟨sched.total, site, sched.located⟩
  obtain ⟨out, run⟩ := run_reference pub tags.length X.positions (callFuel cap) typed phases
    positive
    ordinalFit capCount clock (by unfold callFuel; omega) stable
  have rawReads := selected_reference_reads B f hf T hT X z base raw ds off ts rs ht hr
    (below.trans_lt hh)
  have header : TerminalLink.header pub = (H : Word w) := d.header
  have h32 := d.headerFits
  have headVal : (TerminalLink.header pub).val = H := by
    rw [header, Fin.val_natCast, Nat.mod_eq_of_lt hh]
  have lastVal : (TerminalLink.header pub + 31).val = H + 31 := by
    rw [header, show (31 : Word w) = ((31 : ℕ) : Word w) from rfl, ← Nat.cast_add,
      Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have bodyReads : SourceTransport.Reads (TerminalLink.workerCell (TerminalLink.header pub))
      (eventLog (ts ++ rs)) := by
    intro a v read
    have := rawReads a v read
    simp only [TerminalLink.workerCell, headVal, lastVal]
    omega
  have readFrame := Segment.reads pub tags.length X.positions (callFuel cap) _ run typed phases
    positive ordinalFit capCount clock (by unfold callFuel; omega) stable bodyReads
    (selected_prefix_setup_reads B f hf T hT X z base raw ds d headersBefore ts rs ht hr below)
  have counts : (tags.map (fun l => l.layer.count)).sum = (ls.map Layer.count).sum := by
    rw [← layers, List.map_map]
    rfl
  have num : (ts ++ rs).length = 2 * (ls.map Layer.count).sum := by
    rw [typed.length]
    change ((tagJobs w off cap base tags ++ rowJobs.map rowJob).map Pass.count).sum = _
    rw [List.map_append, List.sum_append, tagCounts, List.map_map, rowCounts, counts, two_mul]
  have hc : (ts ++ rs).length + jobs.length + 1 = calls := by rw [num, phases]
  change after raw (eventLog (ts ++ rs)) = arena at image
  rw [hc, image] at run
  have rawPreserved : ∀ x < base, arena x = raw x := by
    intro x hx
    exact (build_outside ls cap base base _ x (Or.inl hx)).trans
      (write_tags_outside off cap base tags raw x (Or.inl (hx.trans_le (Nat.le_add_left _ _))))
  refine ⟨ts, rs, out, ht, hr, run, ?_, ?_, ?_, ?_, ?_, ?_, readFrame,
    fun _ _ => run.accepted_unique⟩
  · rw [SourceOnline.packet_cost, run.length, run.cost]
    have hL : tags.length ≤ (S.steps + 1) * T + 1 := by
      simp only [tags, selected, List.length_cons, List.length_map]
      exact Nat.succ_le_succ (executeLevels_length B f hf T hT X z)
    have hl : tags.length ≤ visits := hL.trans (Nat.le_mul_of_pos_right _ X.positions_pos)
    have hv : 1 ≤ visits := (Nat.succ_pos _).trans_le (Nat.le_mul_of_pos_right _ X.positions_pos)
    have hcBound : calls ≤ 5 * visits := by
      change ts.length + rs.length ≤ 2 * visits at refCalls
      rw [← hc, List.length_append, phases]; omega
    change countProbes (eventLog (ts++rs)) ≤ (2*cap+4)*visits at refProbes
    calc _ ≤ 5*visits + (257*(5*visits) + (2*cap+4)*visits) :=
              Nat.add_le_add hcBound (Nat.add_le_add (Nat.mul_le_mul_left _ hcBound) refProbes)
         _ = _ := by change _ = (2*cap+1294)*visits; ring
  · intro r hm
    exact ⟨probes_le _, localSegment_event_bound ((runSegment_iff ..).mp run.run).1 _ hm⟩
  · rw [run.memory, ← image]
    exact tagsOK
  · rw [run.memory, ← image]
    exact rowsOK
  · rw [run.memory]
    exact rawPreserved
  · rw [run.memory, ← image]
    exact bitsOK

/-- The selected raw scans and resident header instantiate the complete native
controller. Its charges include both resets at every level and the sentinel. -/
theorem selected_run (pub : Fin 11 → Word w) (F H first pitch : ℕ)
    (d : Resident pub raw H first pitch (words B.recordLimit (selectedLayers B f hf T hT X z) + F)
      B.recordLimit base ⟨leafLayer (siteOrder X), .cursor⟩
      (levelFibers (executeLevels B f hf T hT X z) ds))
    (headersBefore : ∀ j ≤ (executeLevels B f hf T hT X z).length, first + j * pitch + 28 ≤ base)
    (belowHeader : base + 2 * words B.recordLimit (selectedLayers B f hf T hT X z) + F ≤ H)
    (ordinalFit : 2 * (selected B f hf T hT X z).length * (X.positions + 1) < 2 ^ w) :
    let cap := B.recordLimit
    let ls := selectedLayers B f hf T hT X z
    let size := words cap ls
    let off := size + F
    let tags := selected B f hf T hT X z
    let rowJobs := selectedJobs B f hf T hT X z base raw ds
    let calls := 2 * (ls.map Layer.count).sum + 2 * tags.length + 1
    let arena := build cap base base ls (writeTags off cap base tags raw)
    let program := (Native.machine pub).program
    ∃ ts rs out, RolePasses off cap base tags raw ts ∧
      DirectoryRun.Segments rowJobs (after raw (eventLog ts)) rs ∧
      Segment program (callFuel cap) (some 0) none raw arena calls
        (257 * calls + countProbes (eventLog (ts ++ rs))) out ∧
      RAMBuckets.cost Report.probes out ≤ (2 * cap + 1294) *
        (((S.steps + 1) * T + 1) * X.positions) ∧
      (∀ r ∈ out, r.probes ≤ r.events.length ∧ r.events.length < callFuel cap) ∧
      Reads w (after raw (eventLog out)) off cap base tags ∧
      AllRows w (after raw (eventLog out)) cap base base ls ∧
      (∀ x < base, after raw (eventLog out) x = raw x) ∧
      (∀ i < F, after raw (eventLog out) (base + size + i) = raw (base + size + i)) ∧
      ∀ (bits : List (List Bool)) (other : List (Report w)),
        runSegment program (callFuel cap) (some 0) raw bits = some other →
        endState (some 0) other = none → bits = List.replicate calls [] ∧ other = out := by
  obtain ⟨ts, rs, out, ht, hr, seg, cost, per, roles, rows, rawOK, bitsOK, _, unique⟩ :=
    selected_run_with_reads B f hf T hT X z base raw ds pub F H first pitch d headersBefore
      belowHeader ordinalFit
  exact ⟨ts, rs, out, ht, hr, seg, cost, per, roles, rows, rawOK, bitsOK, unique⟩

end PairSimulation.TraversalController

end VPVNP
end Computability
end OAI
