import OAI.Computability.VPVNP.CompressorRecordsOnline

/-!
# Chronological execution of the online descriptor program

Each selected phase contributes the actual branch stream of its worker.
The row input is computed by the recipe in the memory left by the
preceding phase. One final empty-choice calendar call accepts at the
exclusive ordinal bound. The total work bound uses the maximum number
of metadata reads among the fixed recipes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Schedule.Online.Run

open BurstRAM

variable {d initial phases w : ℕ} {C : Catalog d}
variable (plan : Config C initial phases) (ports : Ports w)
local notation "q₀" => initial+phases
local notation "D₀" => N d q₀

/-- The recipe and data worker on this actual path. -/
structure Step (d q w : ℕ) where
  /-- Index of the row recipe chosen by the calendar at this step's ordinal. -/
  phase : Fin q
  /-- The selected worker's directory row, including its entry memory, fuel, branch streams and
  source reports. -/
  row : Directory.Row d w

/-- Each phase starts from actual RAM and has enough private fuel to
evaluate its recipe and to execute each source call. -/
structure Step.Valid (cap : ℕ) (m : Memory w) (step : Step d q₀ w) : Prop where
  phase : (calendar plan).phase (m ports.ordinal.val).val = step.phase.val
  active : m ports.ordinal.val < m ports.rows.val
  input : step.row.input = rowInput plan ports m step.phase
  source : step.row.Valid C ports
  recipeCap : (plan.recipes step.phase).2.code.length+1+2*D₀+5 ≤ cap
  dataCap : step.row.fuel+3+4*((C step.row.worker).params+1)+2*D₀+5 ≤ cap

/-- The next phase is verified in the previous worker's computed post-memory. -/
def Valid (cap : ℕ) : Memory w → List (Step d q₀ w) → Prop
  | m, [] => m ports.rows.val ≤ m ports.ordinal.val
  | m, step :: rest => step.Valid plan ports cap m ∧ Valid cap (post C q₀ ports step.row) rest

/-- Follow the scheduled rows in order and return the memory left when the last worker hands
control back to the calendar. An empty run returns its entry memory. -/
def finalMemory : Memory w → List (Step d q₀ w) → Memory w
  | m, [] => m
  | _, step :: rest => finalMemory (post C q₀ ports step.row) rest

/-- Concatenate the planner, launch, worker and stop reports for each row in its entry memory,
then append the calendar's closing report. -/
def reports : Memory w → List (Step d q₀ w) → List (Report w)
  | m, [] => [linked ports (calendarIndex d q₀) (LevelCalendar.closedReport ports.data m)]
  | m, step :: rest => rowLog plan ports m step.phase step.row ++ reports (post C q₀ ports step.row) rest

/-- Supply empty branch streams for row preparation and stopping, the worker's own streams for
its data calls, and one final empty stream for calendar acceptance. -/
def choices (steps : List (Step d q₀ w)) : List (List Bool) :=
  steps.flatMap (fun step ↦ rowChoices step.row) ++ [[]]

/-- Run the fixed instruction table from the calendar through the terminal
accept. Each phase may depend on choices made inside all earlier workers. -/
theorem execute (steps : List (Step d q₀ w)) (m : Memory w) (state : Word w) (cap : ℕ)
    (htag : m ports.tag.val = LiveStageLink.tagWord w (calendarIndex d q₀)) (fits : D₀ ≤ 2^w)
    (calCap : 30+2*q₀+2*D₀+5 ≤ cap) (launchCap : 20+6*(arity C+1)+2*D₀+5 ≤ cap)
    (v : Valid plan ports cap m steps) :
    runSegment (program plan ports) cap (some state) m (choices steps) = some (reports plan ports m steps) := by
  induction steps generalizing m state with
  | nil =>
    rw [choices,List.flatMap_nil,List.nil_append,runSegment,calendar_stop plan ports state m htag fits v (by omega)]
    rfl
  | cons step rest ih =>
    obtain ⟨hr,ht⟩ := v
    have htag' : post C q₀ ports step.row ports.tag.val = LiveStageLink.tagWord w (calendarIndex d q₀) := by
      simp [post,writeMemory]
    change runSegment _ _ _ _ ((step :: rest).flatMap _ ++ [[]]) = _
    rw [List.flatMap_cons,List.append_assoc, row_segment plan ports state m step.phase step.row hr.input hr.source
      htag fits hr.active hr.phase calCap hr.recipeCap launchCap hr.dataCap]
    change (runSegment _ _ _ _ (choices rest)).map _ = _
    rw [ih _ 0 htag' ht]
    rfl

/-- The full reports leave exactly the memory of the last data worker
after its return to the calendar, and the final call halts. -/
theorem effect (steps : List (Step d q₀ w)) (m : Memory w) (state : Word w) {cap : ℕ}
    (v : Valid plan ports cap m steps) :
    after m (eventLog (reports plan ports m steps)) = finalMemory (C := C) ports m steps ∧
    endState (some state) (reports plan ports m steps) = none := by
  induction steps generalizing m state with
  | nil =>
    have h := terminal_effect (initial := initial) (phases := phases) (d := d) ports m
    exact ⟨by simpa only [reports, finalMemory, eventLog, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] using h.2.1,h.1⟩
  | cons step rest ih =>
    obtain ⟨hr,ht⟩ := v
    obtain ⟨hm,hs⟩ := row_effect plan ports m step.phase step.row hr.input hr.source state
    obtain ⟨hm',hs'⟩ := ih _ 0 ht
    rw [reports, endState_append, hs, finalMemory]
    refine ⟨?_,hs'⟩
    simp only [eventLog,List.flatMap_append,after,List.foldl_append]
    change after (after m (eventLog (rowLog plan ports m step.phase step.row))) _ = _
    rw [hm]
    exact hm'

/-- Uniform metadata-read bound depends only on the finite set of recipes. -/
def maxReads := Finset.univ.sup fun j ↦ (plan.recipes j).2.reads

theorem reads_le (j : Fin q₀) : (plan.recipes j).2.reads ≤ maxReads plan :=
  Finset.le_sup (f := fun i ↦ (plan.recipes i).2.reads) (Finset.mem_univ j)

/-- Sum the number of source-worker calls and their memory probes over all selected rows,
before charging for calendar and dispatch work. -/
def sourceCost (steps : List (Step d q₀ w)) :=
  (steps.map fun step ↦ RAMBuckets.cost Report.probes step.row.reports).sum

/-- Source calls and probes are charged with a catalog-wide constant. Each
scheduled row also pays for the calendar, recipe, frame launch, and closing
call. The final calendar call costs four units including its dispatch read. -/
theorem cost_bound (steps : List (Step d q₀ w)) (m : Memory w) {cap : ℕ}
    (v : Valid plan ports cap m steps) :
    RAMBuckets.cost Report.probes (reports plan ports m steps) ≤
      sourceCost steps*(arity C+3) + steps.length*(maxReads plan+4*arity C+26) + 4 := by
  induction steps generalizing m with
  | nil =>
    rw [reports, RAMBuckets.cost, (terminal_effect (initial := initial) (phases := phases) (d := d) ports m).2.2.1]
    simp [sourceCost,RAMBuckets.cost]
  | cons step rest ih =>
    obtain ⟨hr,ht⟩ := v
    have tail := ih _ ht
    have hlen : step.row.reports.length ≤ RAMBuckets.cost Report.probes step.row.reports := by
      rw [RAMBuckets.cost_eq_length_add_probes]; omega
    have hk := params_le_arity C step.row.worker
    have hm := Nat.mul_le_mul hlen (Nat.add_le_add_right hk 2)
    have hreads := reads_le plan step.phase
    rw [reports, RAMBuckets.cost_append, row_cost plan ports m step.phase step.row hr.source]
    have split : sourceCost (step :: rest) = RAMBuckets.cost Report.probes step.row.reports + sourceCost rest := rfl
    rw [split,Nat.add_mul,List.length_cons,Nat.add_mul,Nat.one_mul]
    have mul : RAMBuckets.cost Report.probes step.row.reports * (arity C+3) =
        RAMBuckets.cost Report.probes step.row.reports * (arity C+2) + RAMBuckets.cost Report.probes step.row.reports :=
      Nat.mul_succ ..
    omega

/-- Number of rows still to be launched from this calendar memory. -/
def remaining (ports : Ports w) (m : Memory w) :=
  (m ports.rows.val).val - (m ports.ordinal.val).val

/-- A per-phase construction can generate the entire path from its current
descriptor memory. It suffices to construct the next source row, preserve
the construction invariant, and account for the single ordinal increment. -/
theorem exists_valid (I : Memory w → Prop) (cap : ℕ)
    (next : ∀ m, I m → m ports.ordinal.val < m ports.rows.val → ∃ step : Step d q₀ w,
      step.Valid plan ports cap m ∧ I (post C q₀ ports step.row) ∧
      remaining ports (post C q₀ ports step.row)+1 = remaining ports m)
    (m : Memory w) (h : I m) :
    ∃ steps, Valid plan ports cap m steps ∧ steps.length = remaining ports m ∧
      I (finalMemory (C := C) ports m steps) := by
  generalize hn : remaining ports m = n
  induction n generalizing m with
  | zero =>
    have hclosed : m ports.rows.val ≤ m ports.ordinal.val :=
      Fin.le_def.mpr (Nat.sub_eq_zero_iff_le.mp hn)
    exact ⟨[],hclosed,rfl,h⟩
  | succ n ih =>
    have hlt : m ports.ordinal.val < m ports.rows.val := Fin.lt_def.mpr (by
      unfold remaining at hn; omega)
    obtain ⟨step,hs,hI,hl⟩ := next m h hlt
    obtain ⟨rest,hr,hcount,hfinal⟩ := ih _ hI (by omega)
    exact ⟨step::rest, ⟨hs,hr⟩, by simp [hcount], hfinal⟩

/-- Acceptance, exact path choices, final invariant and work bound follow
from the next-row construction without a precomputed directory of rows. -/
theorem exists_run (I : Memory w → Prop) (cap : ℕ)
    (next : ∀ m, I m → m ports.ordinal.val < m ports.rows.val → ∃ step : Step d q₀ w,
      step.Valid plan ports cap m ∧ I (post C q₀ ports step.row) ∧
      remaining ports (post C q₀ ports step.row)+1 = remaining ports m)
    (m : Memory w) (h : I m) (state : Word w)
    (htag : m ports.tag.val = LiveStageLink.tagWord w (calendarIndex d q₀)) (fits : D₀ ≤ 2^w)
    (calCap : 30+2*q₀+2*D₀+5 ≤ cap) (launchCap : 20+6*(arity C+1)+2*D₀+5 ≤ cap) :
    ∃ steps : List (Step d q₀ w),
      let rs := reports plan ports m steps
      steps.length = remaining ports m ∧
      runSegment (program plan ports) cap (some state) m (choices steps) = some rs ∧
      branchPaths rs = choices steps ∧ endState (some state) rs = none ∧
      I (after m (eventLog rs)) ∧
      RAMBuckets.cost Report.probes rs ≤
        sourceCost steps*(arity C+3) + steps.length*(maxReads plan+4*arity C+26) + 4 := by
  obtain ⟨steps,hv,hlen,hfinal⟩ := exists_valid plan ports I cap next m h
  have he := execute plan ports steps m state cap htag fits calCap launchCap hv
  obtain ⟨hm,hs⟩ := effect plan ports steps m state hv
  exact ⟨steps,hlen,he,((runSegment_iff ..).mp he).2.2,hs,hm ▸ hfinal,cost_bound plan ports steps m hv⟩

end CompressorRecords.Schedule.Online.Run

end VPVNP
end Computability
end OAI
