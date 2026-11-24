import OAI.Computability.VPVNP.CompressorSlotPhaseCosts
import OAI.Computability.VPVNP.CompressorFlatRowWorker
import OAI.Computability.VPVNP.CompressorShrinkABSliceVisits
import OAI.Computability.VPVNP.CompressorSurvivingNative
import OAI.Computability.VPVNP.CompressorSourceWalk

/-!
# Traffic of the flattened slice workers

All AB operands are affine functions of the global bundle ordinal. The
flattening prologue uses registers for these operands. Each surviving-role
worker reads the selected term and writes the thirteen cells of a piece.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScheduledRates

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM ShrinkABSliceRecipe SliceRAM
open PhaseCosts ShrinkSliceSweep

variable {w : ℕ}

private theorem affineProbes {k : ℕ} (pub : FlatRows.Public k w) (s : Word w) (m : Memory w) :
    countProbes (FlatRows.events (fun _ => false) pub s m) = 0 := by
  have h (is : List (Fin (k+1))) :
      countProbes (is.flatMap (FlatRows.operandEvents (fun _ => false) pub s m)) = 0 := by
    induction is with
    | nil => rfl
    | cons i is ih => rw [List.flatMap_cons,Greedy.probes_append,ih,Nat.add_zero]; rfl
  rw [FlatRows.events,Greedy.probes_append,Greedy.probes_append,h]; rfl

open private execute_reads execute_stores wordStores reads from
  OAI.Computability.VPVNP.CompressorSlicePairVisit

/-- A pair visit charges four input probes and at most three writes, including
successful executions at the machine's arithmetic boundary. -/
private theorem pairProbes (p : Fin 6 → Word w) (s : Word w) (m : Memory w) (r : Report w)
    (hr : execute (IndexedPair.table.instantiate w p).program 38
      ((IndexedPair.table.instantiate w p).program.start s)
      m [] = some r) : r.probes ≤ 7 := by
  rw [execute_reads p s m 14,execute_stores p s m _ rfl rfl] at hr
  obtain rfl := Option.some.inj hr
  change countProbes (reads p s m ++ wordStores _ _ _ _ _) ≤ 7
  rw [Greedy.probes_append,show countProbes (reads p s m) = 4 from rfl]
  have bound (a s t lo hi : Word w) : countProbes (wordStores a s t lo hi) ≤ 3 := by
    unfold wordStores; split <;> first | exact (le_refl 3) | exact (by decide : 1 ≤ 3)
  exact Nat.add_le_add_left (bound ..) 4

/-- Probe count is unchanged when direct affine operands prepare the flattened
call. Its instruction overhead is already included in the execution budget. -/
private theorem flatProbes {r p k : ℕ} (core : Template p r k) (fuel limit : ℕ)
    (one : ∀ (u : Fin k → Word w) x mem rep, execute (core.instantiate w u).program fuel
      ((core.instantiate w u).program.start x) mem [] = some rep → rep.probes ≤ limit)
    (bank : FlatRows.Public k w) (m : Memory w) (st : Word w) (rep : Report w) :
    let P := ((FlatRows.compile core (fun _ => false)).instantiate w bank).program
    execute P (fuel+(3+7*(k+1))) (P.start st) m [] = some rep → rep.probes ≤ limit := by
  intro P run
  rw [FlatRows.execute_flat] at run
  obtain ⟨localReport,hl,rfl⟩ := Option.map_eq_some_iff.mp run
  change countProbes (_++localReport.events) ≤ limit
  rw [Greedy.probes_append,affineProbes,Nat.zero_add]; exact one _ _ _ _ hl

/-- The three different AB row workers have their own input arities. -/
def abFuel {m n : ℕ} : Stage m n → ℕ
  | .clear _ => 25
  | .pair _ => 90
  | .refs _ => 95

/-- Maximum probes for one AB slice visit, one to clear a count and seven to test a pair or
update its references. -/
def abProbeCap {m n : ℕ} : Stage m n → ℕ
  | .clear _ => 1
  | .pair _ | .refs _ => 7

private theorem abOne {m n : ℕ} (I : Inputs) (j : Stage m n)
    (bank : Fin (stage I j).worker.params → Word w) (mem : Memory w) (st : Word w)
      (rep : Report w) :
    let P := ((stage I j).worker.table.instantiate w bank).program
    execute P (abFuel j) (P.start st) mem [] = some rep → rep.probes ≤ abProbeCap j := by
  cases j with
  | clear i =>
    apply flatProbes (template clearOps 0) 8 1 _ bank mem st rep
    intro u x m r hr
    have he := clearVisit_native (u 0) x m
    have single : (fun _ : Fin 1 => u 0) = u := funext (fun i => by fin_cases i; rfl)
    rw [single] at he
    rw [he] at hr; cases hr; exact le_rfl
  | pair i => exact flatProbes IndexedPair.table 38 7 pairProbes bank mem st rep
  | refs i =>
    apply flatProbes adjTemplate 36 7 _ bank mem st rep
    intro u x m r hr
    rw [adjVisit_native u m x] at hr
    cases hr
    change countProbes _ ≤ 7
    rw [(adjEvents_work u m x).1]; split <;> decide

private theorem boundedScan {C : Type*} {P : BurstRAM.Program w C} {fuel limit calls : ℕ}
    (s : Option (Word w))
    (one : ∀ mem st rep, execute P fuel (P.start st) mem [] = some rep → rep.probes ≤ limit)
    (mem : Memory w) (rs : List (Report w)) (run : runSegment P fuel s mem
      (List.replicate calls []) = some rs) :
    RAMBuckets.cost Report.probes rs ≤ (1+limit)*calls := by
  induction calls generalizing s mem rs with
  | zero => have h : rs = [] := (Option.some.inj run).symm; simp [h]
  | succ n ih =>
    cases s with
    | none => simp [List.replicate_succ,runSegment] at run
    | some st =>
      rw [List.replicate_succ,runSegment] at run
      cases he : execute P fuel (P.start st) mem [] with
      | none => simp [he] at run
      | some r =>
        rw [he] at run
        obtain ⟨more,hm,rfl⟩ := Option.map_eq_some_iff.mp run
        have hp := one mem st r he
        have ht := ih _ _ more hm
        rw [RAMBuckets.cost,Nat.mul_succ]; omega

/-- The actual AB stage table runs once over all global bundle ordinals. This
accepts the physical operands installed by the scheduled recipe. -/
def ABSource {m n : ℕ} (I : Inputs) (rows : ℕ) (j : Stage m n) (mem : Memory w)
    (rs : List (Report w)) : Prop :=
  ∃ bank : Fin (stage I j).worker.params → Word w,
    runSegment ((stage I j).worker.table.instantiate w bank).program (abFuel j)
      (some 0) mem (List.replicate rows []) = some rs

private theorem abWalk {m n rows : ℕ} (I : Inputs) {js : List (Stage m n)} {mem : Memory w}
    {rs : List (Report w)}
    (h : SourceWalk (ABSource I rows) js mem rs) :
    rs.length = rows*js.length ∧
      RAMBuckets.cost Report.probes rs ≤ rows*(js.map (fun j ↦ 1+abProbeCap j)).sum ∧
      ∀ r ∈ rs, r.events.length+1 ≤ 95 := by
  induction h with
  | done => simp
  | @next j js mem rs more src _ ih =>
    obtain ⟨bank,run⟩ := src
    have n := (run_length run).trans (List.length_replicate ..)
    have c := boundedScan _ (abOne I j bank) _ _ run
    refine ⟨?_,?_,?_⟩
    · rw [List.length_append,n,ih.1,List.length_cons,Nat.mul_succ,Nat.add_comm]
    · rw [RAMBuckets.cost_append,List.map_cons,List.sum_cons,Nat.mul_add]
      exact Nat.add_le_add (c.trans_eq (Nat.mul_comm ..)) ih.2.1
    · intro rep hr
      rcases List.mem_append.mp hr with ha|hb
      · exact (run_cap run rep ha).trans (by cases j <;> simp only [abFuel] <;> decide)
      · exact ih.2.2 _ hb

/-- Whole-level AB table, with a fixed number of scheduler visits independent of the
number of bundles and of their selected widths. -/
theorem flatABCounts {m n rows : ℕ} (I : Inputs) {mem : Memory w} {rs : List (Report w)}
    (h : SourceWalk (ABSource I rows) (phases m n) mem rs) :
    rs.length = rows*(m+n+2*(m*n)) ∧
      RAMBuckets.cost Report.probes rs ≤ rows*(2*(m+n)+16*(m*n)) ∧
      ∀ r ∈ rs, r.events.length+1 ≤ 95 := by
  obtain ⟨len,work,cap⟩ := abWalk I h
  have hl := visits_length I m n
  rw [visits,List.length_map] at hl
  rw [hl] at len
  have weight : ((phases m n).map (fun j => 1+abProbeCap j)).sum = 2*(m+n)+16*(m*n) := by
    simp only [phases,List.map_append,List.sum_append,List.map_map]
    change ((List.finRange (m+n)).map (fun _ => 2)).sum +
      ((List.finRange (m*n)).map (fun _ => 8)).sum +
      ((List.finRange (m*n)).map (fun _ => 8)).sum = _
    simp [List.map_const']; ring
  rw [weight] at work
  exact ⟨len,work,cap⟩

private theorem flatTotal {r p k : ℕ} (core : Template p r k) (fuel : ℕ)
    (one : ∀ (u : Fin k → Word w) st mem, ∃ rep, execute (core.instantiate w u).program fuel
      ((core.instantiate w u).program.start st) mem [] = some rep)
    (bank : FlatRows.Public k w) (mem : Memory w) (st : Word w) :
    let P := ((FlatRows.compile core (fun _ => false)).instantiate w bank).program
    ∃ rep, execute P (fuel+(3+7*(k+1))) (P.start st) mem [] = some rep := by
  intro P
  let v := FlatRows.value (fun _ => false) bank st mem
  obtain ⟨r,h⟩ := one (fun j => v j.castSucc) (v (Fin.last k)) mem
  rw [FlatRows.execute_flat,h]; exact ⟨_,rfl⟩

private theorem abTotal {m n : ℕ} (I : Inputs) (j : Stage m n)
    (bank : Fin (stage I j).worker.params → Word w)
    (mem : Memory w) (st : Word w) :
    let P := ((stage I j).worker.table.instantiate w bank).program
    ∃ rep, execute P (abFuel j) (P.start st) mem [] = some rep := by
  cases j with
  | clear i =>
    apply flatTotal (template clearOps 0) 8 _ bank mem st
    intro u x m
    have h := clearVisit_native (u 0) x m
    rw [show (fun _ : Fin 1 => u 0) = u from funext fun j => by fin_cases j; rfl] at h
    exact ⟨_,h⟩
  | pair i =>
    apply flatTotal IndexedPair.table 38 _ bank mem st
    intro u x m
    rw [execute_reads u x m 14,execute_stores u x m _ rfl rfl]; exact ⟨_,rfl⟩
  | refs i =>
    apply flatTotal adjTemplate 36 _ bank mem st
    intro u x m; exact ⟨_,adjVisit_native u m x⟩

private theorem useFixedFuel {C : Type*} (P : BurstRAM.Program w C) {fixed cap n : ℕ}
    (total : ∀ m s, ∃ r, execute P fixed (P.start s) m [] = some r)
    {s : Option (Word w)} {m : Memory w} {rs : List (Report w)}
    (run : runSegment P cap s m (List.replicate n []) = some rs) :
    runSegment P fixed s m (List.replicate n []) = some rs := by
  induction n generalizing s m rs with
  | zero => exact run
  | succ n ih =>
    cases s with
    | none => simp [List.replicate_succ,runSegment] at run
    | some st =>
      rw [List.replicate_succ,runSegment] at run ⊢
      cases hc : execute P cap (P.start st) m [] with
      | none => simp [hc] at run
      | some r =>
        rw [hc] at run
        obtain ⟨t,ht,rfl⟩ := Option.map_eq_some_iff.mp run
        obtain ⟨s,hs⟩ := total m st
        have eqn : s = r := (execute_prefix_unique hs (suffix := []) hc).2
        rw [hs,eqn]
        change (runSegment P fixed r.result (after m r.events) (List.replicate n [])).map
          (r :: ·) = _
        rw [ih ht]; rfl

/-- Each successful planner row can be replayed at its fixed worker-specific fuel,
including when the external scheduler supplied a larger uniform allowance. -/
theorem abSourceOfScheduled {m n rows cap : ℕ} (I : Inputs) (pub : Fin 5 → Word w) (state : Word w)
    (ref : Memory w) {j : Stage m n} {mem : Memory w} {rs : List (Report w)}
    (source : ShrinkABSliceRecipe.Source I pub state ref rows cap j mem rs) : ABSource I rows j
      mem rs :=
  ⟨fun i => ((stage I j).params i).eval pub state ref,useFixedFuel _ (abTotal I j _) source⟩

/-- Resource count on the exact full AB calendar walk generated by its planner. -/
theorem scheduledABCounts {m n rows cap : ℕ} (I : Inputs) (pub : Fin 5 → Word w) (state : Word w)
    (ref : Memory w) {mem : Memory w} {rs : List (Report w)}
    (h : SourceWalk (ShrinkABSliceRecipe.Source I pub state ref rows cap) (phases m n) mem rs) :
    rs.length = rows*(m+n+2*(m*n)) ∧ RAMBuckets.cost Report.probes rs ≤ rows*(2*(m+n)+16*(m*n)) ∧
      ∀ r ∈ rs, r.events.length+1 ≤ 95 := by
  apply flatABCounts (mem := mem) I
  generalize phases m n = js at h ⊢
  induction h with
  | done => exact .done _
  | next head _ tail => exact .next (abSourceOfScheduled I pub state ref head) tail

/-- The selected supply worker uses four reads and thirteen writes for every
physical motif piece. Its event count is independent of payload width. -/
theorem survivingCounts {M : ℕ} (subdiv : Fin 4 → ℕ) (banks : Fin 4 → SurvivingNative.Public w)
    (mem : Fin 4 → Memory w) (rs : Fin 4 → List (Report w))
    (run : ∀ t, runSegment ((SurvivingNative.pass.table.instantiate w (banks t)).program)
      (1 + SurvivingNative.ops.length) (some 0) (mem t) (List.replicate (M * subdiv t) []) = some
        (rs t)) :
    (∑ t, (rs t).length) = M*(∑ t, subdiv t) ∧
      (∑ t, RAMBuckets.cost Report.probes (rs t)) = 18*M*(∑ t, subdiv t) ∧
      ∀ t, ∀ r ∈ rs t, r.events.length+1 = 1+SurvivingNative.ops.length := by
  have count (t : Fin 4) := fixedScanCounts (fun m s ↦ (SurvivingNative.report
    (banks t) s m).events)
    (fun m s ↦ by
      obtain ⟨he,ret,_⟩ := SurvivingNative.native (banks t) s m
      rw [he,← ret]) (fun m s ↦
      let h := SurvivingNative.native (banks t) s m
      ⟨h.2.2.2.2.1,h.2.2.2.1⟩) (run t)
  refine ⟨?_,?_,?_⟩
  · simp only [(count _).1,Finset.mul_sum]
  · simp only [(count _).2.1,Nat.mul_assoc,Finset.mul_sum]
  · intro t r hr; rw [(count t).2.2.2 r hr,Nat.add_comm]

end CompressorRecords.ScheduledRates

end VPVNP
end Computability
end OAI
