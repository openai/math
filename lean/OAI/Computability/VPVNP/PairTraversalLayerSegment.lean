import OAI.Computability.VPVNP.PairTraversalNativeLayer
import OAI.Computability.VPVNP.PairTraversalSiteWorker

/-!
# Consecutive reset-entry calls for one traversal layer

The persistent word counts the sites already translated. Every call starts
with fresh private registers and memory and reads the raw rows that remain
below the descriptor arena. The sequence constructs the exact descriptor
image used by the traversal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows

open BurstRAM CompressorRecords
open scoped Fin.CommRing

variable {w : ℕ} {C : Type*}

/-- The native site worker reads one row from its directory, publishes its
descriptor, and returns the successor cursor. -/
def SiteWorkerRun (P : BurstRAM.Program w C) (fuel : ℕ) (L : Layer) (cap previous base : ℕ)
    (counts starts : Fin L.count → Word w) : Prop :=
  ∀ (i : Fin L.count) (mem : Memory w), rowRepresents mem (counts i) (starts i)
    ((L.ids i).map (fun j : ℕ => (j : Word w))) →
    ∃ es, execute P fuel (P.start (i.val : Word w)) mem [] =
        some ⟨es, some ((i.val : Word w) + 1)⟩ ∧
      after mem es = DescriptorRows.passMemory mem (address cap base i.val) (starts i).val
        (address cap base i.val + 2) (counts i) (previous : Word w) ((cap + 2 : ℕ) : Word w)
        (L.ids i).length ∧
      countProbes es = 2 * (L.ids i).length + 3 ∧ es.length = 7 * (L.ids i).length + 24

private theorem finRange_numbers (n : ℕ) : (List.finRange n).map Fin.val = List.range' 0 n := by
  rw [← List.range_eq_range']
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp

open private pass_outside live append_probes from OAI.Computability.VPVNP.PairTraversalLayerExecution

private theorem realize_passes {L : Layer} {cap previous base : ℕ} {state : Word w}
    {priv : Word w → Word w} {counts starts : Fin L.count → Word w}
    {P : BurstRAM.Program w C} {fuel : ℕ}
    (worker : SiteWorkerRun P fuel L cap previous base counts starts)
    (countBefore : ∀ i, (counts i).val < base)
    (sourceBefore : ∀ i, (starts i).val + (L.ids i).length ≤ base)
    {xs : List (Fin L.count)} {mem : Memory w} {es : List (Event w)}
    (passes : LayerPasses L cap previous base state priv counts starts xs mem es)
    (row : ∀ i, rowRepresents mem (counts i) (starts i) ((L.ids i).map (fun j : ℕ => (j : Word w))))
    (start : ℕ) (order : xs.map Fin.val = List.range' start xs.length) :
    ∃ rs, runSegment P fuel (some (start : Word w)) mem (List.replicate xs.length []) = some rs ∧
      endState (some (start : Word w)) rs = some ((start + xs.length : ℕ) : Word w) ∧
      after mem (eventLog rs) = after mem es ∧ countProbes (eventLog rs) = countProbes es ∧
      List.Forall₂ (fun (rep : Report w) (i : Fin L.count) =>
        rep.probes = 2 * (L.ids i).length + 3 ∧ rep.events.length = 7 * (L.ids i).length + 24)
        rs xs := by
  induction passes generalizing start with
  | nil m => exact ⟨[], rfl, by simp [endState], rfl, rfl, .nil⟩
  | @cons i is m ss es site tail ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at order
    rcases order with ⟨rfl, remaining⟩
    obtain ⟨ev, executeSite, image, probes, steps⟩ := worker i m (row i)
    let rep : Report w := ⟨ev, some ((i.val : Word w) + 1)⟩
    have equalMemory : after m ev = after m ss := by
      rw [image, site.memory, List.length_map]
    have same (x : ℕ) (h : x < base) : after m ss x = m x := by
      apply pass_outside site x
      intro inside
      exact h.not_ge ((Nat.le_add_right base _).trans inside.1)
    have rowsNext (j : Fin L.count) : rowRepresents (after m ss) (counts j) (starts j)
        ((L.ids j).map (fun a : ℕ => (a : Word w))) := by
      refine ⟨(congrArg Fin.val (same _ (countBefore j))).trans (row j).1, fun p => ?_⟩
      have hp : p.val < (L.ids j).length := by simpa only [List.length_map] using p.isLt
      exact (same _ ((Nat.add_lt_add_left hp _).trans_le (sourceBefore j))).trans ((row j).2 p)
    obtain ⟨rs, segment, final, replay, cost, calls⟩ := ih rowsNext (i.val + 1) remaining
    have next : some ((i.val : Word w) + 1) = some ((i.val + 1 : ℕ) : Word w) := by simp
    refine ⟨rep :: rs, ?_, ?_, ?_, ?_, .cons ⟨probes, steps⟩ calls⟩
    · rw [List.length_cons, List.replicate_succ, runSegment, executeSite]
      change (runSegment P fuel (some ((i.val : Word w) + 1)) (after m ev)
        (List.replicate is.length [])).map (rep :: ·) = _
      rw [equalMemory, next, segment]
      rfl
    · change endState (some ((i.val : Word w) + 1)) rs = _
      rw [next, final, List.length_cons, Nat.add_right_comm, Nat.add_assoc]
    · change after m (ev ++ eventLog rs) = after m (ss ++ es)
      rw [show after m (ev ++ eventLog rs) = after (after m ev) (eventLog rs)
          from List.foldl_append,
        show after m (ss ++ es) = after (after m ss) es from List.foldl_append, equalMemory]
      exact replay
    · change countProbes (ev ++ eventLog rs) = countProbes (ss ++ es)
      rw [append_probes, append_probes, cost, probes, site.probes, List.length_map]

/-- Run one call for every site from cursor zero. Each report's instruction and
probe counts are tied to that site's actual number of children. -/
theorem run_numbered_layer (P : BurstRAM.Program w C) (fuel : ℕ) (L : Layer) (cap previous base : ℕ)
    (counts starts : Fin L.count → Word w) (mem : Memory w)
    (worker : SiteWorkerRun P fuel L cap previous base counts starts)
    (rows : ∀ i, rowRepresents mem (counts i) (starts i)
      ((L.ids i).map (fun j : ℕ => (j : Word w))))
    (countBefore : ∀ i, (counts i).val < base)
    (sourceBefore : ∀ i, (starts i).val + (L.ids i).length ≤ base)
    (capacity : ∀ i, (L.ids i).length ≤ cap) (fit : endPos cap base L < 2 ^ w) :
    ∃ rs, runSegment P fuel (some 0) mem (List.replicate L.count []) = some rs ∧
      endState (some 0) rs = some (L.count : Word w) ∧
      after mem (eventLog rs) = writeLayer cap previous base L mem ∧
      countProbes (eventLog rs) = 2 * (∑ i, (L.ids i).length) + 3 * L.count ∧
      rs.length = L.count ∧
      List.Forall₂ (fun (rep : Report w) (i : Fin L.count) =>
        rep.probes = 2 * (L.ids i).length + 3 ∧ rep.events.length = 7 * (L.ids i).length + 24)
        rs (List.finRange L.count) := by
  obtain ⟨es, passes, image, cost⟩ := native_layer L cap previous base 0 (fun _ => 0)
    counts starts mem rows countBefore sourceBefore capacity fit
  obtain ⟨rs, run, final, replay, probes, calls⟩ := realize_passes worker countBefore sourceBefore
    passes rows 0 (by simpa only [List.length_finRange] using finRange_numbers L.count)
  exact ⟨rs, by simpa using run, by simpa using final, replay.trans image, probes.trans cost,
    calls.length_eq.trans List.length_finRange, calls⟩

/-- The first three words address the raw counts and preimage array. The
remaining words address the old and new descriptor layers at their common stride. -/
def workerData (pub : Fin 6 → Word w) (cap previous base : ℕ) : Fin 6 → Word w :=
  ![pub 3, pub 5, pub 4, (previous : Word w), (base : Word w), ((cap + 2 : ℕ) : Word w)]

open private row_end_le from OAI.Computability.VPVNP.PairTraversalRows

/-- The same six-parameter instruction table realizes every site in a directory. -/
theorem directory_worker (pub : Fin 6 → Word w) (L : Layer) (cap previous base : ℕ)
    (sourceBefore : ∀ i : Fin L.count, (rowAt pub (i.val : Word w)).val + (L.ids i).length ≤ base)
    (capacity : ∀ i, (L.ids i).length ≤ cap) (fit : endPos cap base L < 2 ^ w) :
    let M := (SiteWorker.program.template (some 6)).instantiate w (workerData pub cap previous base)
    SiteWorkerRun M.program (7 * cap + 25) L cap previous base
      (fun i => countAt pub (i.val : Word w)) (fun i => rowAt pub (i.val : Word w)) := by
  let data := workerData pub cap previous base
  dsimp only
  intro i mem row
  let src := (rowAt pub (i.val : Word w)).val
  let node := address cap base i.val
  have hs : SiteWorker.source data (i.val : Word w) = (src : Word w) :=
    Fin.ext (Nat.mod_eq_of_lt (rowAt pub (i.val : Word w)).isLt).symm
  have hn : SiteWorker.node data (i.val : Word w) = (node : Word w) := by
    change (base : Word w) + (i.val : Word w) * ((cap + 2 : ℕ) : Word w) =
      ((base + (cap + 2) * i.val : ℕ) : Word w)
    simp only [Nat.cast_add, Nat.cast_mul]
    rw [mul_comm]
  have cnt : (mem (SiteWorker.counter data (i.val : Word w)).val).val = (L.ids i).length := by
    change (mem (countAt pub (i.val : Word w)).val).val = _
    simpa only [List.length_map] using row.1
  have within : node + 2 + (L.ids i).length < 2 ^ w := by
    have := row_end_le cap base L i
    have := capacity i
    dsimp only [node]
    omega
  exact SiteWorker.native data (i.val : Word w) mem src node (L.ids i).length (7 * cap + 25)
    hs hn cnt ((sourceBefore i).trans (Nat.le_add_right _ _)) within (by have := capacity i; omega)

open NetworkKernel LocalHistory

variable {A : Type*} [CommRing A] {Label : Type} [Fintype Label] {κ : Label → A}
variable {N : Network} {t : Term A N}

open private valid_owner from OAI.Computability.VPVNP.PairTraversalNativeLayer

open Classical in
/-- The fixed site worker runs from cursor zero through a selected term's entire
output layer, with one reset-entry call per new site. -/
theorem run_step_layer (old : Order N.Site) (next : Order t.output.Site) (r : TermParsers κ t)
    (physical : Word w → Word w) (realizes : RepresentsPlacement old next t.place physical)
    (hchildren : ∀ v, r.order.children v = old.restrict (fun u => v = t.place u))
    (pub : Fin 6 → Word w) (mem : Memory w) (oldCount : (pub 0).val = old.length)
    (newCount : (pub 2).val = next.length) (collected : PreimagesAt pub physical mem old.length)
    (cap previous base : ℕ) (regions : RowRegions pub)
    (inputEnd : (pub 5).val + (pub 2).val * (pub 4).val ≤ base)
    (capacity : ∀ i, ((stepLayer old next r).ids i).length ≤ min (pub 4).val cap)
    (fit : endPos cap base (stepLayer old next r) < 2 ^ w) :
    let L := stepLayer old next r
    let M := (SiteWorker.program.template (some 6)).instantiate w (workerData pub cap previous base)
    ∃ rs, runSegment M.program (7 * cap + 25) (some 0) mem (List.replicate next.length []) =
        some rs ∧
      endState (some 0) rs = some (next.length : Word w) ∧
      after mem (eventLog rs) = writeLayer cap previous base L mem ∧
      countProbes (eventLog rs) = 2 * old.length + 3 * next.length ∧ rs.length = next.length ∧
      List.Forall₂ (fun (rep : Report w) (i : Fin next.length) =>
        rep.probes = 2 * (L.ids i).length + 3 ∧ rep.events.length = 7 * (L.ids i).length + 24)
        rs (List.finRange next.length) := by
  let L := stepLayer old next r
  have before (i : Fin L.count) := preimage_input_before regions inputEnd (valid_owner newCount i)
  have hs (i : Fin L.count) : (rowAt pub (i.val : Word w)).val + (L.ids i).length ≤ base :=
    (Nat.add_le_add_left ((le_min_iff.mp (capacity i)).1) _).trans (before i).2
  have hc (i : Fin L.count) : (L.ids i).length ≤ cap := (le_min_iff.mp (capacity i)).2
  obtain ⟨rs, run, final, image, probes, count, calls⟩ := run_numbered_layer _ _ L cap previous base
    _ _ mem (directory_worker pub L cap previous base hs hc fit)
    (raw_rows_of_preimages old next r physical realizes hchildren pub mem oldCount newCount
      collected)
    (fun i => (before i).1) hs hc fit
  refine ⟨rs, run, final, image, ?_, count, calls⟩
  have h : ∑ i : Fin L.count, (L.ids i).length = old.length := stepLayer_sum_ids_length old next r
  rw [probes, h]
  rfl

end PairSimulation.TraversalRows

end VPVNP
end Computability
end OAI
