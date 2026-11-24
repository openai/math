import OAI.Computability.VPVNP.LiveHeaderProgram
import OAI.Computability.VPVNP.LiveStageSegments
import OAI.Computability.VPVNP.LiveHeaderBoundedRun

/-!
# Composing native live-header stages on shared external memory

The source executions use their own seventeen-word parameter rows. At every
accepting boundary the native linker updates the reserved tag word and resets
the cursor. The combined report records each dispatch read and each handoff
write, with an exact cost in calls and external probes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule

variable {w : ℕ}

/-- Row relocation preserves the native segment of the small stage table. -/
theorem run_component (s : Sizes) (base : ℕ) (i : StageId) (fuel : ℕ) (st : Option (Word w))
    (m : Memory w) (bits : List (List Bool)) :
    runSegment ((component i).instantiate w (bank w s base)).program fuel st m bits =
      runSegment ((stageTemplate (stage i)).2.instantiate w (rowData w s base (stage i))).program fuel st m bits := by
  induction bits generalizing st m with
  | nil => rfl
  | cons b bits ih =>
    cases st with
    | none => rfl
    | some st =>
      simp only [runSegment, component_start]
      cases execute ((stageTemplate (stage i)).2.instantiate w (rowData w s base (stage i))).program fuel
        (((stageTemplate (stage i)).2.instantiate w (rowData w s base (stage i))).program.start st) m b <;> simp only [ih]

/-- Embed a complete native stage segment in the fixed header register file. -/
theorem run_entry {p r k : ℕ} (T : Template p r k) (hr : r ≤ 50) (hk : k ≤ 17)
    (pub : Fin 17 → Word w) (fuel : ℕ) (st : Option (Word w)) (m : Memory w) (bits : List (List Bool)) :
    runSegment ((entry T hr hk).2.instantiate w pub).program fuel st m bits =
      runSegment (T.instantiate w (pub ∘ includeFin hk)).program fuel st m bits := by
  induction bits generalizing st m with
  | nil => rfl
  | cons b bits ih =>
    cases st with
    | none => rfl
    | some st =>
      simp only [runSegment, entry_start]
      cases execute (T.instantiate w (pub ∘ includeFin hk)).program fuel
        ((T.instantiate w (pub ∘ includeFin hk)).program.start st) m b <;> simp only [ih]

/-- Reports and branch choices of a complete source stage. -/
structure StageTrace (w : ℕ) where
  /-- The header stage whose source reports this trace records. -/
  id : StageId
  /-- The source-stage clock used to execute the recorded calls. -/
  fuel : ℕ
  /-- The private choice tape supplied to each successive source-stage call. -/
  paths : List (List Bool)
  /-- The ordered source reports returned by the recorded calls before linker dispatch and
  handoff events. -/
  reports : List (Report w)

/-- The source reports wrapped with the header linker's dispatch and stage-transfer events. -/
def StageTrace.output (x : StageTrace w) (addr : Word w) : List (Report w) :=
  x.reports.map (LiveStageLink.linkedReport next addr x.id)

/-- The source cost plus a dispatch probe per report and a transfer probe when the stage has a
successor. -/
def StageTrace.cost (x : StageTrace w) :=
  RAMBuckets.cost Report.probes x.reports + x.reports.length + (if (next x.id).isSome then 1 else 0)

/-- The memory after the source reports and the linker's transfer to the next header stage. -/
def StageTrace.finalMem (x : StageTrace w) (addr : Word w) (m : Memory w) : Memory w :=
  LiveStageLink.transferMemory addr (next x.id) (after m (eventLog x.reports))

/-- Source runs in the prescribed order, each with its fresh cursor and the
memory actually passed from its predecessor. -/
inductive StageRuns (s : Sizes) (base : ℕ) :
    Option StageId → Memory w → List (StageTrace w) → Prop
  | done (m : Memory w) : StageRuns s base none m []
  | cons (x : StageTrace w) {m : Memory w} {xs : List (StageTrace w)}
      (source : runSegment ((stageTemplate (stage x.id)).2.instantiate w (rowData w s base (stage x.id))).program
        x.fuel (some 0) m x.paths = some x.reports)
      (accept : endState (some 0) x.reports = none)
      (frame : LiveStageLink.PreservesTagOnReturns (Fin.ofNat _ base) m x.reports)
      (rest : StageRuns s base (next x.id) (x.finalMem (Fin.ofNat _ base) m) xs) :
      StageRuns s base (some x.id) m (x :: xs)

/-- Replay a list of header stages in order, including the transfer writes between stages. -/
def finalMemory (addr : Word w) (m : Memory w) (xs : List (StageTrace w)) : Memory w :=
  xs.foldl (fun mem x => x.finalMem addr mem) m

/-- Every linked call corresponds to one source call; there are no extra
handoff calls between stages. -/
theorem calls_output (addr : Word w) (xs : List (StageTrace w)) :
    (xs.flatMap (fun x => x.output addr)).length = (xs.map (fun x => x.reports.length)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.map_cons, List.sum_cons]
    simp [StageTrace.output]

/-- Execute a complete suffix of the scheduled native header program with
the original branch inputs. The accepted output and its cost are exact. -/
theorem run_of_stages (s : Sizes) (base cap : ℕ) (hfits : stages.length ≤ 2^w) {id : Option StageId}
    {m : Memory w} {xs : List (StageTrace w)} (h : StageRuns s base id m xs)
    (hroom : ∀ x ∈ xs, x.fuel + 2*stages.length+5 ≤ cap)
    (htag : ∀ i, id = some i → m (Fin.ofNat (2^w) base).val = LiveStageLink.tagWord w i) :
    let addr : Word w := Fin.ofNat _ base
    let out := xs.flatMap (fun x => x.output addr)
    let st := id.map (fun _ => (0 : Word w))
    runSegment (program.instantiate w (publicData w s base)).program cap st m (xs.flatMap StageTrace.paths) = some out ∧
    endState st out = none ∧ after m (eventLog out) = finalMemory addr m xs ∧
    RAMBuckets.cost Report.probes out = (xs.map StageTrace.cost).sum := by
  induction h with
  | done m => exact ⟨rfl, rfl, rfl, rfl⟩
  | @cons x m xs source accept frame rest ih =>
    let addr : Word w := Fin.ofNat _ base
    have hc := (run_component s base x.id x.fuel (some 0) m x.paths).trans source
    obtain ⟨hr, hs, hm, hcost⟩ := LiveStageLink.runSegment_accepting component next
      (bank w s base) addr x.id hfits (hroom x (by simp)) 0 m x.paths x.reports
      (htag x.id rfl) frame hc accept
    change runSegment (program.instantiate w (publicData w s base)).program cap (some 0) m x.paths = some (x.output addr) at hr
    change endState (some 0) (x.output addr) = _ at hs
    change after m (eventLog (x.output addr)) = x.finalMem addr m at hm
    change RAMBuckets.cost Report.probes (x.output addr) = x.cost at hcost
    have htag' : ∀ i, next x.id = some i → x.finalMem addr m addr.val = LiveStageLink.tagWord w i := by
      intro i hi
      unfold StageTrace.finalMem
      rw [hi, LiveStageLink.transferMemory_tag]
    obtain ⟨hr', hs', hm', hcost'⟩ := ih (fun y hy => hroom y (List.mem_cons_of_mem _ hy)) htag'
    change runSegment _ cap (some 0) m (x.paths ++ xs.flatMap StageTrace.paths) =
        some (x.output addr ++ xs.flatMap (fun y => y.output addr)) ∧
      endState (some 0) (x.output addr ++ xs.flatMap (fun y => y.output addr)) = none ∧
      after m (eventLog (x.output addr ++ xs.flatMap (fun y => y.output addr))) = finalMemory addr m (x::xs) ∧
      RAMBuckets.cost Report.probes (x.output addr ++ xs.flatMap (fun y => y.output addr)) = (List.map StageTrace.cost (x :: xs)).sum
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [PrimedSchedule.runSegment_append, hr]
      simp only [Option.bind_some, hs, hm]
      rw [hr']
      rfl
    · rw [endState_append, hs]
      exact hs'
    · have hsplit (a b : List (Report w)) : after m (eventLog (a++b)) =
          after (after m (eventLog a)) (eventLog b) := by simp [eventLog,after,List.foldl_append]
      rw [hsplit, hm]
      exact hm'
    · rw [RAMBuckets.cost_append, hcost, hcost']
      rfl

/-- The suffix of the header schedule starting at the given stage, empty after completion. -/
def remainingStages (id : Option StageId) : List Stage :=
  match id with
  | some i => stages.drop i.val
  | none => []

private theorem remaining_next (i : StageId) : remainingStages (some i) = stage i :: remainingStages (next i) := by
  change stages.drop i.val = stage i :: _
  rw [List.drop_eq_getElem_cons i.isLt]
  congr 1
  unfold next
  split_ifs with h
  · rfl
  · exact List.drop_eq_nil_of_le (Nat.le_of_not_gt h)

/-- Accepted execution traverses precisely the suffix prescribed by the
header's sequential successor, even when a scan has zero active entries. -/
theorem StageRuns.schedule {s : Sizes} {base : ℕ} {id : Option StageId} {m : Memory w}
    {xs : List (StageTrace w)} (h : StageRuns s base id m xs) :
    xs.map (fun x => stage x.id) = remainingStages id := by
  induction h with
  | done => rfl
  | cons x _ _ _ _ ih => simp only [List.map_cons, ih, remaining_next]

private theorem rawCost (rs : List (Report w)) (hp : ∀ r ∈ rs, r.probes ≤ 6) :
    RAMBuckets.cost Report.probes rs ≤ 7*rs.length := by
  induction rs with
  | nil => simp [RAMBuckets.cost]
  | cons r rs ih =>
    have hr := hp r (by simp)
    have hb := ih fun t ht => hp t (List.mem_cons_of_mem _ ht)
    simp only [RAMBuckets.cost, List.length_cons]
    omega

private theorem sum_le_map {α : Type*} (a b : α → ℕ) (xs : List α) (h : ∀ x ∈ xs, a x ≤ b x) :
    (xs.map a).sum ≤ (xs.map b).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x (by simp)) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- Bounds for the full program at the prescribed entry. The second inequality
also budgets two enclosing-dispatch probes per header call. -/
theorem complete_budget (s : Sizes) (base : ℕ) {m : Memory w} {xs : List (StageTrace w)}
    (h : StageRuns s base (some (⟨0, by decide⟩ : StageId)) m xs)
    (hl : ∀ x ∈ xs, x.reports.length ≤ calls s (stage x.id))
    (hp : ∀ x ∈ xs, ∀ rep ∈ x.reports, rep.probes ≤ probes (stage x.id)) :
    (xs.map (fun x => x.reports.length)).sum ≤ callBound s ∧
    (xs.map StageTrace.cost).sum + 2*(xs.map (fun x => x.reports.length)).sum ≤ costBound s := by
  have sched : xs.map (fun x => stage x.id) = stages := h.schedule
  have hs : (xs.map (fun x => calls s (stage x.id))).sum = callBound s := by
    simpa only [← sched, List.map_map, Function.comp_def] using sum_calls s
  have hl' := sum_le_map (fun x : StageTrace w => x.reports.length) (fun x => calls s (stage x.id)) xs hl
  rw [hs] at hl'
  have estimate (x : StageTrace w) (hx : x ∈ xs) : x.cost ≤ 9 * x.reports.length := by
    have hr := rawCost x.reports fun r hmem => (hp x hx r hmem).trans (probe_limit (stage x.id))
    have hn : 0 < x.reports.length := by
      have positive {idx : Option StageId} {mem : Memory w} {ys : List (StageTrace w)}
          (hsteps : StageRuns s base idx mem ys) : ∀ y ∈ ys, y.reports ≠ [] := by
        induction hsteps with
        | done => simp
        | cons y _ accept _ _ ih =>
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · intro he; rw [he] at accept; contradiction
          · exact ih z hz
      exact List.length_pos_iff.mpr (positive h x hx)
    unfold StageTrace.cost
    split <;> omega
  have hsum := sum_le_map StageTrace.cost (fun x => 9*x.reports.length) xs estimate
  have distrib (ys : List (StageTrace w)) :
      (ys.map (fun x => 9*x.reports.length)).sum = 9 * (ys.map (fun x => x.reports.length)).sum := by
    induction ys with
    | nil => rfl
    | cons x ys ih => simp [ih, Nat.mul_add]
  rw [distrib] at hsum
  exact ⟨hl', by unfold costBound; omega⟩

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
