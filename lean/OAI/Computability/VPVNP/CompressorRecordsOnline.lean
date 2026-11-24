import OAI.Computability.VPVNP.CompressorRecordsLevelCalendar
import OAI.Computability.VPVNP.CompressorRecordsDirectory
import OAI.Computability.VPVNP.CompressorRecordsRowRecipe

/-!
# Native online descriptor program

Stage zero launches the freshly constructed row. The data workers come
next, followed by the calendar and the row recipes. A data worker's
closing call returns to the calendar. A recipe's accepting call returns
to stage zero, which snapshots its actual output row. The calendar is the
only accepting terminal stage of the scheduled path.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Schedule.Online

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {d initial phases w : ℕ} {C : Catalog d}

/-- The finite plan of row-building recipes for the initial and repeated phases, together with
the number of levels advanced by each block. -/
structure Config (C : Catalog d) (initial phases : ℕ) where
  /-- How many level headers the calendar advances when it moves to the next block. -/
  levelsPerBlock : ℕ
  /-- The recipe and its register count at each initial or repeated phase, producing a
  directory row of the catalog's fixed arity. -/
  recipes : Fin (initial+phases) → Σ r, RowRecipe.Recipe r 5 (arity C)

variable (plan : Config C initial phases)

/-- Total number of linked online stages, including a launcher, the data workers, a calendar
and the row recipes. -/
abbrev N (d q : ℕ) := (d+1)+(q+1)
local notation "q₀" => initial+phases
local notation "D₀" => N d q₀

/-- Build the planner calendar for this configuration using the catalog's row pitch and the
configured number of levels per block. -/
def calendar := LevelCalendar.recipeCalendar d initial phases (arity C+3) plan.levelsPerBlock

/-- Stage zero, where the controller snapshots the directory row and launches its data worker. -/
def launchIndex (d q : ℕ) : Fin (N d q) := (0 : Fin (d+1)).castAdd (q+1)
/-- The linked stage of a data worker, immediately following the launcher in catalog order. -/
def workerIndex (q : ℕ) (i : Fin d) : Fin (N d q) := i.succ.castAdd (q+1)
/-- The stage after the data-worker bank that selects the next planner recipe. -/
def calendarIndex (d q : ℕ) : Fin (N d q) := (0 : Fin (q+1)).natAdd (d+1)
/-- The linked stage of a row-building recipe, numbered after the calendar. -/
def recipeIndex (d : ℕ) {q : ℕ} (j : Fin q) : Fin (N d q) := j.succ.natAdd (d+1)

private def fullSlot {p r : ℕ} (T : Template p r 5) : Slot := ⟨⟨p,r,5,T⟩,id⟩
private def dataSlot (P : Pass) : Slot := ⟨worker P,fun _ ↦ 0⟩

/-- The stage slots and their operand mappings, ordered as launcher, data workers, calendar and
row recipes. -/
def slots : Fin D₀ → Slot :=
  Fin.addCases (Fin.cons (fullSlot (Controller.table (arity C))) (fun i ↦ dataSlot (C i)))
    (Fin.cons (fullSlot (LevelCalendar.table (calendar plan))) (fun j ↦ fullSlot (plan.recipes j).2.acceptTable))

private def regs := Finset.univ.sup fun s ↦ (slots plan s).regs
private def embedRegs (s : Fin D₀) : Fin (slots plan s).regs ↪ Fin (regs plan) :=
  Fin.castLEEmb (Finset.le_sup (f := fun t ↦ (slots plan t).regs) (Finset.mem_univ s))

/-- Embed each stage's instructions into the online program's shared register bank and public
operand table. -/
def tables (s : Fin D₀) := LiveStageLink.widen (slots plan s).table (embedRegs plan s) (slots plan s).publicIndex

/-- The continuation on stage acceptance. A completed worker goes to the calendar and a
completed recipe goes to the launcher. -/
def handoff (d q : ℕ) : Fin (N d q) → Option (Fin (N d q)) :=
  Fin.addCases (Fin.cons none (fun _ ↦ some (calendarIndex d q))) (Fin.cons none (fun _ ↦ some (launchIndex d q)))

/-- The fixed online RAM template linking the widened stage tables with their accepting
handoffs. -/
def template := LiveStageLink.linked (tables plan) (handoff d q₀)

/-- Instantiate the linked online stages with the runtime workspace ports and stage-tag
address. -/
def program (ports : Ports w) := (LiveStageLink.machine (tables plan) (handoff d q₀) ports.data ports.tag).program

/-- Wrap a source-stage report in the online dispatcher's events and apply the accepting
handoff for its stage. -/
def linked (ports : Ports w) (s : Fin D₀) (rep : Report w) :=
  LiveStageLink.linkedReport (handoff d q₀) ports.tag s rep

private def source (slot : Slot) (ports : Ports w) (state : Word w) (m : Memory w) (bs : List Bool) (f : ℕ) :=
  let P := (slot.table.instantiate w (ports.data ∘ slot.publicIndex)).program
  execute P f (P.start state) m bs

private theorem call (ports : Ports w) (s : Fin D₀) (state : Word w) (m : Memory w) (bs : List Bool)
    (htag : m ports.tag.val = LiveStageLink.tagWord w s) (fits : D₀ ≤ 2^w)
    {f cap : ℕ} (hcap : f+2*D₀+5 ≤ cap) {rep : Report w}
    (hr : source (slots plan s) ports state m bs f = some rep) :
    execute (program plan ports) cap ((program plan ports).start state) m bs =
      some (linked ports s rep) := by
  apply LiveStageLink.execute_linked_of_stage _ _ _ _ s fits hcap _ _ htag bs rep
  rw [tables, LiveStageLink.execute_widen_start]
  exact hr

theorem phase_count : (calendar plan).size = q₀ := by
  simp [calendar, LevelCalendar.recipeCalendar, LevelCalendar.Calendar.size]

/-- Identify a recipe's configuration index with its slot in the constructed planner calendar. -/
def phaseIndex (j : Fin q₀) : Fin (calendar plan).size := Fin.cast (phase_count plan).symm j

theorem phase_tag (j : Fin q₀) :
    LiveStageLink.tagWord w ((calendar plan).planner (phaseIndex plan j)).succ =
      LiveStageLink.tagWord w (recipeIndex d j) := by
  apply congrArg (Fin.ofNat (2^w))
  apply (LevelCalendar.recipe_tag d initial phases (arity C+3) plan.levelsPerBlock (phaseIndex plan j)).trans
  simp [phaseIndex,recipeIndex]
  omega

/-- One real calendar call selects the next row recipe in the shared tag
cell and returns the header pointer to it. -/
theorem calendar_call (ports : Ports w) (state : Word w) (m : Memory w) (j : Fin q₀)
    (htag : m ports.tag.val = LiveStageLink.tagWord w (calendarIndex d q₀)) (fits : D₀ ≤ 2^w)
    (active : m ports.ordinal.val < m ports.rows.val)
    (hj : (calendar plan).phase (m ports.ordinal.val).val = j.val)
    {cap : ℕ} (hcap : 30+2*q₀+2*D₀+5 ≤ cap) :
    execute (program plan ports) cap ((program plan ports).start state) m [] =
      some (linked ports (calendarIndex d q₀)
        (LevelCalendar.dispatchReport (calendar plan) ports.data m (phaseIndex plan j))) := by
  apply call plan ports _ state m [] htag fits hcap
  simp only [slots, calendarIndex, Fin.addCases_right, Fin.cons_zero]
  apply LevelCalendar.execute_dispatch (calendar plan) ports.data state m [] active (phaseIndex plan j) hj
  · rw [phase_count]; unfold N at fits; omega
  · rw [phase_count]

theorem calendar_stop (ports : Ports w) (state : Word w) (m : Memory w)
    (htag : m ports.tag.val = LiveStageLink.tagWord w (calendarIndex d q₀)) (fits : D₀ ≤ 2^w)
    (stop : m ports.rows.val ≤ m ports.ordinal.val) {cap : ℕ} (hcap : 6+2*D₀+5 ≤ cap) :
    execute (program plan ports) cap ((program plan ports).start state) m [] =
      some (linked ports (calendarIndex d q₀) (LevelCalendar.closedReport ports.data m)) := by
  apply call plan ports _ state m [] htag fits hcap
  simp only [slots, calendarIndex, Fin.addCases_right, Fin.cons_zero]
  exact LevelCalendar.execute_closed (calendar plan) ports.data state m [] stop le_rfl

/-- The accepting source report of a row recipe, using the write events computed from the block
header state and entry memory. -/
def recipeSource (ports : Ports w) (j : Fin q₀) (state : Word w) (m : Memory w) : Report w :=
  ⟨((plan.recipes j).2.report ports.data state m).events,none⟩

/-- A fixed recipe runs on the returned header pointer and transfers to the
row launcher. -/
theorem recipe_call (ports : Ports w) (j : Fin q₀) (state : Word w) (m : Memory w)
    (htag : m ports.tag.val = LiveStageLink.tagWord w (recipeIndex d j)) (fits : D₀ ≤ 2^w)
    {cap : ℕ} (hcap : (plan.recipes j).2.code.length+1+2*D₀+5 ≤ cap) :
    execute (program plan ports) cap ((program plan ports).start state) m [] =
      some (linked ports (recipeIndex d j) (recipeSource plan ports j state m)) := by
  apply call plan ports _ state m [] htag fits hcap
  simp only [slots,recipeIndex,Fin.addCases_right,Fin.cons_succ]
  exact RowRecipe.execute_accept (plan.recipes j).2 ports.data state m [] _ (Nat.lt_succ_self _)

/-- Stage zero loads the currently addressed row and installs its worker's
parameter frame. -/
theorem launch_call (ports : Ports w) (state : Word w) (m : Memory w)
    (htag : m ports.tag.val = 0) (fits : D₀ ≤ 2^w)
    (active : m ports.ordinal.val < m ports.rows.val) {cap : ℕ}
    (hcap : 20+6*(arity C+1)+2*D₀+5 ≤ cap) :
    execute (program plan ports) cap ((program plan ports).start state) m [] =
      some (linked ports (launchIndex d q₀) (Controller.rowReport (arity C) ports.data m)) := by
  apply call plan ports (launchIndex d q₀) state m [] htag fits hcap
  simp only [slots,launchIndex,Fin.addCases_left,Fin.cons_zero]
  exact Controller.execute_row (arity C) ports.data state m [] _ active le_rfl

/-- The data worker's closing source report, including the active-frame loads for its bound and
parameters before acceptance. -/
def closedSource (P : Pass) (ports : Ports w) (m : Memory w) :=
  LiveStageLink.prependLog (Frame.loadEvents ports.activeFrame m 0 (P.params+1)) (LiveHeaderBounded.closedReport w)

theorem worker_active (ports : Ports w) (i : Fin d) (state : Word w) (m : Memory w) (bs : List Bool)
    (htag : m ports.tag.val = LiveStageLink.tagWord w i.succ) (fits : D₀ ≤ 2^w)
    (guard : state < stopWord ports.activeFrame m) {f cap : ℕ}
    (hcap : f+3+4*((C i).params+1)+2*D₀+5 ≤ cap) (rep : Report w)
    (hr : let S := ((C i).table.instantiate w (parameters ports.activeFrame m)).program
      execute S f (S.start state) m bs = some rep) :
    execute (program plan ports) cap ((program plan ports).start state) m bs =
      some (linked ports (workerIndex q₀ i) (workerReport (C i) ports.activeFrame m rep)) := by
  apply call plan ports _ state m bs htag fits hcap
  simp only [slots,workerIndex,Fin.addCases_left,Fin.cons_succ]
  change execute (((worker (C i)).table.instantiate w (fun _ ↦ ports.activeFrame)).program) _
    (((worker (C i)).table.instantiate w (fun _ ↦ ports.activeFrame)).program.start state) m bs = _
  rw [execute_worker _ _ _ _ _ guard,hr]
  rfl

theorem worker_stop (ports : Ports w) (i : Fin d) (state : Word w) (m : Memory w)
    (htag : m ports.tag.val = LiveStageLink.tagWord w i.succ) (fits : D₀ ≤ 2^w)
    (guard : stopWord ports.activeFrame m ≤ state) {cap : ℕ}
    (hcap : 4+4*((C i).params+1)+2*D₀+5 ≤ cap) :
    execute (program plan ports) cap ((program plan ports).start state) m [] =
      some (linked ports (workerIndex q₀ i) (closedSource (C i) ports m)) := by
  apply call plan ports _ state m [] htag fits hcap
  simp only [slots,workerIndex,Fin.addCases_left,Fin.cons_succ]
  exact execute_worker_stop (C i) ports.activeFrame state m [] guard 0

private theorem returned (ports : Ports w) (index : Fin D₀) (m : Memory w) (rep : Report w)
    {st : Word w} (hs : rep.result = some st) :
    let out := linked ports index rep
    out.result = some st ∧ after m out.events = after m rep.events ∧
      out.probes = rep.probes+1 ∧ choiceBits out.events = choiceBits rep.events := by
  refine ⟨?_,?_,?_,LiveStageLink.linkedReport_choiceBits ..⟩
  · simp [linked, LiveStageLink.linkedReport, LiveStageLink.prependLog, LiveStageLink.exitReport, hs]
  · rw [linked,LiveStageLink.linkedReport_after,hs]
  · rw [linked,LiveStageLink.linkedReport_probes,hs]; simp

private theorem transferred (ports : Ports w) (index dest : Fin D₀) (m : Memory w) (rep : Report w)
    (hs : rep.result = none) (hd : handoff d q₀ index = some dest) :
    let out := linked ports index rep
    out.result = some 0 ∧ after m out.events = writeMemory (after m rep.events) ports.tag
      (LiveStageLink.tagWord w dest) ∧ out.probes = rep.probes+2 ∧ choiceBits out.events = choiceBits rep.events := by
  refine ⟨?_,?_,?_,LiveStageLink.linkedReport_choiceBits ..⟩
  · simp [linked, LiveStageLink.linkedReport, LiveStageLink.prependLog, LiveStageLink.exitReport, hs, hd]
  · rw [linked, LiveStageLink.linkedReport_after,hs,hd]
  · rw [linked, LiveStageLink.linkedReport_probes,hs,hd]; simp

/-- The linked calendar report dispatching the recipe for the specified phase. -/
def calendarReport (ports : Ports w) (m : Memory w) (j : Fin q₀) :=
  linked ports (calendarIndex d q₀) (LevelCalendar.dispatchReport (calendar plan) ports.data m (phaseIndex plan j))

/-- The linked report of a recipe that writes its row and hands control to the launcher. -/
def recipeReport (ports : Ports w) (j : Fin q₀) (state : Word w) (m : Memory w) :=
  linked ports (recipeIndex d j) (recipeSource plan ports j state m)

/-- The linked controller report that installs the newly prepared row and dispatches its data
worker. -/
def launchReport (C : Catalog d) (q : ℕ) (ports : Ports w) (m : Memory w) :=
  LiveStageLink.linkedReport (handoff d q) ports.tag (launchIndex d q) (Controller.rowReport (arity C) ports.data m)

/-- Wrap one successful data call with its active-frame loads and the online stage dispatch. -/
def activeReport (C : Catalog d) (q : ℕ) (ports : Ports w) (i : Fin d) (m : Memory w) (rep : Report w) :=
  LiveStageLink.linkedReport (handoff d q) ports.tag (workerIndex q i) (workerReport (C i) ports.activeFrame m rep)

/-- The linked closing report at the worker's exclusive bound, handing control back to the
calendar. -/
def stopReport (C : Catalog d) (q : ℕ) (ports : Ports w) (i : Fin d) (m : Memory w) :=
  LiveStageLink.linkedReport (handoff d q) ports.tag (workerIndex q i) (closedSource (C i) ports m)

theorem calendar_effect (ports : Ports w) (m : Memory w) (j : Fin q₀) :
    let out := calendarReport plan ports m j
    out.result = some (LevelCalendar.header (calendar plan) ports.data m) ∧
      after m out.events = writeMemory m ports.tag (LiveStageLink.tagWord w (recipeIndex d j)) ∧
      out.probes = 5 ∧ choiceBits out.events = [] := by
  obtain ⟨hm,hr,hp,hb⟩ := LevelCalendar.dispatch_effect (calendar plan) ports.data m (phaseIndex plan j)
  obtain ⟨hs,he,hc,hk⟩ := returned ports (calendarIndex d q₀) m _ hr
  rw [phase_tag plan] at hm
  exact ⟨hs,he.trans hm,hc.trans (by rw [hp]),hk.trans hb⟩

theorem recipe_effect (ports : Ports w) (j : Fin q₀) (s : Word w) (m : Memory w) :
    let R := (plan.recipes j).2
    let out := recipeReport plan ports j s m
    out.result = some 0 ∧ after m out.events =
      writeMemory (Greedy.writeRow m (R.address ports.data s m) (R.words ports.data s m)) ports.tag 0 ∧
      out.probes = R.reads+(arity C+3)+2 ∧ choiceBits out.events = [] := by
  obtain ⟨hs,he,hp,hb⟩ := transferred ports (recipeIndex d j) (launchIndex d q₀) m
    (recipeSource plan ports j s m) rfl (by simp [handoff,recipeIndex])
  obtain ⟨_,hc,hk⟩ := RowRecipe.report_cost (plan.recipes j).2 ports.data s m
  exact ⟨hs, he.trans (congrArg (fun mem ↦ writeMemory mem ports.tag 0) (RowRecipe.after_row ..)),
    hp.trans (congrArg (·+2) hc), hb.trans hk⟩

theorem launch_effect (ports : Ports w) (m : Memory w) :
    let out := launchReport C q₀ ports m
    out.result = some (Directory.start C ports m) ∧ after m out.events = Directory.prepared C ports m ∧
      out.probes = 7+2*(arity C+1) ∧ choiceBits out.events = [] := by
  obtain ⟨hr,hm,hp,hb⟩ := returned ports (launchIndex d q₀) m (Controller.rowReport (arity C) ports.data m) rfl
  obtain ⟨_,hc,hk⟩ := Controller.rowReport_cost (arity C) ports.data m
  exact ⟨hr,hm,hp.trans (by change countProbes _+1 = _; rw [hc]; omega),hb.trans hk⟩

theorem active_effect (ports : Ports w) (i : Fin d) (m : Memory w) (rep : Report w)
    {s : Word w} (h : rep.result = some s) :
    let out := activeReport C q₀ ports i m rep
    out.result = some s ∧ after m out.events = after m rep.events ∧
      out.probes = rep.probes+(C i).params+2 ∧ choiceBits out.events = choiceBits rep.events := by
  have cost := Frame.frame_cost ports.activeFrame m 0 ((C i).params+1) (LiveHeaderBounded.activeReport rep)
  obtain ⟨hr,hm,hp,hb⟩ := returned ports (workerIndex q₀ i) m (workerReport (C i) ports.activeFrame m rep) h
  exact ⟨hr, hm.trans cost.2.2.2.1, hp.trans (by rw [workerReport,cost.2.1]; change _ + rep.probes + 1 = _; omega),
    hb.trans cost.2.2.1⟩

theorem stop_effect (ports : Ports w) (i : Fin d) (m : Memory w) :
    let out := stopReport C q₀ ports i m
    out.result = some 0 ∧ after m out.events = writeMemory m ports.tag (LiveStageLink.tagWord w (calendarIndex d q₀)) ∧
      out.probes = (C i).params+3 ∧ choiceBits out.events = [] := by
  have cost := Frame.frame_cost ports.activeFrame m 0 ((C i).params+1) (LiveHeaderBounded.closedReport w)
  obtain ⟨hr,hm,hp,hb⟩ := transferred ports (workerIndex q₀ i) (calendarIndex d q₀) m
    (closedSource (C i) ports m) rfl (by simp [workerIndex,handoff])
  exact ⟨hr,hm.trans (congrArg (fun mem ↦ writeMemory mem ports.tag _) cost.2.2.2.1),
    hp.trans (by rw [closedSource,cost.2.1]; rfl), hb.trans cost.2.2.1⟩

theorem terminal_effect (ports : Ports w) (m : Memory w) :
    let out := linked ports (calendarIndex d q₀) (LevelCalendar.closedReport ports.data m)
    out.result = none ∧ after m out.events = m ∧ out.probes = 3 ∧ choiceBits out.events = [] := by
  have hn : handoff d q₀ (calendarIndex d q₀) = none := by simp [handoff,calendarIndex]
  dsimp only
  refine ⟨?_,?_,?_,LiveStageLink.linkedReport_choiceBits ..⟩
  · simp [linked,LiveStageLink.linkedReport, LiveStageLink.prependLog, LiveStageLink.exitReport, hn]
    rfl
  · rw [linked,LiveStageLink.linkedReport_after,hn]; rfl
  · rw [linked,LiveStageLink.linkedReport_probes,hn]; rfl

/-- Wrap the worker reports in execution order, advancing the source memory after each call so
the next frame is read from its actual entry memory. -/
def workerRows (C : Catalog d) (q : ℕ) (ports : Ports w) (i : Fin d) :
    Memory w → List (Report w) → List (Report w)
  | _, [] => []
  | m, rep :: rs => activeReport C q ports i m rep :: workerRows C q ports i (after m rep.events) rs

/-- Run all the source calls of a data worker, acknowledge its stop, and
continue at the calendar tag. Each read of the bounded frame uses the
memory left by the preceding source call. -/
theorem worker_segment (ports : Ports w) (i : Fin d) (pub : Fin (C i).params → Word w)
    (bound st : Word w) (m : Memory w) (bits : List (List Bool)) (rs : List (Report w))
    (f cap : ℕ) (hf : 0 < f) (fits : D₀ ≤ 2^w)
    (hcap : f+3+4*((C i).params+1)+2*D₀+5 ≤ cap)
    (hr : runSegment ((C i).table.instantiate w pub).program f (some st) m bits = some rs)
    (hv : ValidTrace C i ports pub bound st m rs) (tail : List (List Bool)) :
    let D := program plan ports
    let finalMem := after m (eventLog rs)
    runSegment D cap (some st) m (bits ++ [] :: tail) =
      (runSegment D cap (some 0) (writeMemory finalMem ports.tag (LiveStageLink.tagWord w (calendarIndex d q₀))) tail).map
        (fun more ↦ workerRows C q₀ ports i m rs ++ stopReport C q₀ ports i finalMem :: more) := by
  dsimp only
  induction bits generalizing st m rs with
  | nil =>
    obtain rfl : rs = [] := (Option.some.inj hr).symm
    obtain ⟨⟨htag,hbound,_⟩,hle⟩ := hv
    have hc := worker_stop plan ports i st m htag fits (hbound ▸ hle) (cap := cap) (by omega)
    have he := stop_effect (C := C) (initial := initial) (phases := phases) ports i m
    change runSegment _ _ _ _ ([] :: tail) = _
    rw [runSegment,hc]
    change (runSegment _ _ (stopReport C q₀ ports i m).result (after m (stopReport C q₀ ports i m).events) tail).map _ = _
    rw [he.1,he.2.1]; rfl
  | cons bs rest ih =>
    rw [runSegment] at hr
    let S := ((C i).table.instantiate w pub).program
    cases hs : execute S f (S.start st) m bs with
    | none => rw [hs] at hr; contradiction
    | some rep =>
      rw [hs] at hr
      obtain ⟨reps,hr',rfl⟩ := Option.map_eq_some_iff.mp hr
      obtain ⟨⟨htag,hbound,hpub⟩,hlt,next,hn,hv'⟩ := hv
      have hsource : let P := ((C i).table.instantiate w (parameters ports.activeFrame m)).program
          execute P f (P.start st) m bs = some rep := by rw [hpub]; exact hs
      have hc := worker_active plan ports i st m bs htag fits (hbound ▸ hlt) hcap rep hsource
      have he := active_effect (initial := initial) (phases := phases) ports i m rep hn (C := C)
      rw [List.cons_append,runSegment,hc]
      change (runSegment _ _ (activeReport C q₀ ports i m rep).result
        (after m (activeReport C q₀ ports i m rep).events) _).map _ = _
      rw [he.1,he.2.1,ih next (after m rep.events) reps (hn ▸ hr') hv']
      simp only [workerRows, List.cons_append, Option.map_map, Function.comp_def, eventLog,
        List.flatMap_cons, after, List.foldl_append]
      rfl

/-- Memory after calendar dispatch has written the selected recipe's stage tag. -/
def calendarMemory (ports : Ports w) (m : Memory w) (j : Fin q₀) :=
  writeMemory m ports.tag (LiveStageLink.tagWord w (recipeIndex d j))

/-- Memory after the selected recipe writes its row at the computed address and sets the
launcher tag. -/
def rowInput (ports : Ports w) (m : Memory w) (j : Fin q₀) : Memory w :=
  let pre := calendarMemory (d := d) ports m j
  let s := LevelCalendar.header (calendar plan) ports.data m
  let R := (plan.recipes j).2
  writeMemory (Greedy.writeRow pre (R.address ports.data s pre) (R.words ports.data s pre)) ports.tag 0

/-- The calendar dispatch, recipe execution and worker launch reports that precede the data
calls of one online row. -/
def preparation (ports : Ports w) (m : Memory w) (j : Fin q₀) : List (Report w) :=
  [calendarReport plan ports m j,
   recipeReport plan ports j (LevelCalendar.header (calendar plan) ports.data m) (calendarMemory (d := d) ports m j),
   launchReport C q₀ ports (rowInput plan ports m j)]

/-- Execute the calendar, its selected recipe, and the launcher, then enter
the data worker selected by the computed row. The launcher reads the
actual output memory of the selected recipe. -/
theorem prepare_segment (ports : Ports w) (state : Word w) (m : Memory w) (j : Fin q₀)
    (htag : m ports.tag.val = LiveStageLink.tagWord w (calendarIndex d q₀)) (fits : D₀ ≤ 2^w)
    (active : m ports.ordinal.val < m ports.rows.val)
    (hj : (calendar plan).phase (m ports.ordinal.val).val = j.val)
    (activeRow : rowInput plan ports m j ports.ordinal.val < rowInput plan ports m j ports.rows.val)
    {cap : ℕ} (calCap : 30+2*q₀+2*D₀+5 ≤ cap)
    (recipeCap : (plan.recipes j).2.code.length+1+2*D₀+5 ≤ cap)
    (launchCap : 20+6*(arity C+1)+2*D₀+5 ≤ cap) (tail : List (List Bool)) :
    let input := rowInput plan ports m j
    let D := program plan ports
    runSegment D cap (some state) m ([] :: [] :: [] :: tail) =
      (runSegment D cap (some (Directory.start C ports input)) (Directory.prepared C ports input) tail).map
        (preparation plan ports m j ++ ·) := by
  let pre := calendarMemory (d := d) ports m j
  let s := LevelCalendar.header (calendar plan) ports.data m
  let input := rowInput plan ports m j
  have cal := calendar_call plan ports state m j htag fits active hj calCap
  have recp := recipe_call plan ports j s pre (by simp [pre,calendarMemory,writeMemory]) fits recipeCap
  have launch := launch_call plan ports 0 input (by simp [input,rowInput,writeMemory]) fits activeRow launchCap
  have hc := calendar_effect plan ports m j
  have hr := recipe_effect plan ports j s pre
  have hl := launch_effect (C := C) (initial := initial) (phases := phases) ports input
  change runSegment _ _ _ _ (_ :: _ :: _ :: tail) = _
  rw [runSegment,cal]
  change (runSegment _ _ (calendarReport plan ports m j).result (after m (calendarReport plan ports m j).events) _).map _ = _
  rw [hc.1,hc.2.1]
  change (runSegment _ _ (some s) pre ([] :: [] :: tail)).map _ = _
  rw [runSegment,recp]
  change ((runSegment _ _ (recipeReport plan ports j s pre).result (after pre (recipeReport plan ports j s pre).events) _).map _).map _ = _
  rw [hr.1,hr.2.1]
  change ((runSegment _ _ (some 0) input ([] :: tail)).map _).map _ = _
  rw [runSegment,launch]
  change (((runSegment _ _ (launchReport C q₀ ports input).result (after input (launchReport C q₀ ports input).events) tail).map _).map _).map _ = _
  rw [hl.1,hl.2.1]
  simp only [Option.map_map,preparation,List.cons_append,List.nil_append,Function.comp_def]
  rfl

/-- All reports for one online row, including preparation, the ordered data calls and the
closing return to the calendar. -/
def rowLog (ports : Ports w) (m : Memory w) (j : Fin q₀) (row : Directory.Row d w) :=
  preparation plan ports m j ++ workerRows C q₀ ports row.worker (row.dataMemory C ports) row.reports ++
    [stopReport C q₀ ports row.worker (row.endMemory C ports)]

/-- The row's final worker memory with the stage tag set to resume the calendar. -/
def post (C : Catalog d) (q : ℕ) (ports : Ports w) (row : Directory.Row d w) :=
  writeMemory (row.endMemory C ports) ports.tag (LiveStageLink.tagWord w (calendarIndex d q))

/-- The complete choice-stream list for the row, with empty streams for its three preparation
calls and its closing call. -/
def rowChoices (row : Directory.Row d w) := [] :: [] :: [] :: (row.choices ++ [[]])

/-- A complete phase begins and ends at the calendar. The original source
call sequence consumes exactly its own branch choices. The recipe and row
launcher operate on the memory computed by the preceding phase. -/
theorem row_segment (ports : Ports w) (state : Word w) (m : Memory w) (j : Fin q₀)
    (row : Directory.Row d w) (input : row.input = rowInput plan ports m j)
    (v : row.Valid C ports)
    (htag : m ports.tag.val = LiveStageLink.tagWord w (calendarIndex d q₀)) (fits : D₀ ≤ 2^w)
    (active : m ports.ordinal.val < m ports.rows.val) (hj : (calendar plan).phase (m ports.ordinal.val).val = j.val)
    {cap : ℕ} (calCap : 30+2*q₀+2*D₀+5 ≤ cap)
    (recipeCap : (plan.recipes j).2.code.length+1+2*D₀+5 ≤ cap)
    (launchCap : 20+6*(arity C+1)+2*D₀+5 ≤ cap)
    (dataCap : row.fuel+3+4*((C row.worker).params+1)+2*D₀+5 ≤ cap)
    (tail : List (List Bool)) :
    let D := program plan ports
    runSegment D cap (some state) m (rowChoices row ++ tail) =
      (runSegment D cap (some 0) (post C q₀ ports row) tail).map (rowLog plan ports m j row ++ ·) := by
  have prep := prepare_segment plan ports state m j htag fits active hj (input ▸ v.active) calCap recipeCap launchCap
    (row.choices ++ [] :: tail)
  rw [← input] at prep
  have hw := worker_segment plan ports row.worker (Directory.words C ports row.worker row.input)
    (Directory.bound C ports row.input) (Directory.start C ports row.input) (row.dataMemory C ports)
    row.choices row.reports row.fuel cap v.positiveFuel fits dataCap v.sourceRun v.frame tail
  change runSegment _ _ _ _ (rowChoices row ++ tail) = _
  simp only [rowChoices, List.cons_append, List.nil_append, List.append_assoc]
  rw [prep]
  change (runSegment _ _ _ (row.dataMemory C ports) _).map _ = _
  rw [hw]
  simp only [rowLog,post,Directory.Row.endMemory,Option.map_map,Function.comp_def,List.append_assoc,
    List.cons_append,List.nil_append]

private theorem workerRows_cost (ports : Ports w) (i : Fin d) (pub : Fin (C i).params → Word w)
    (bound st : Word w) (m : Memory w) (rs : List (Report w))
    (h : ValidTrace C i ports pub bound st m rs) :
    RAMBuckets.cost Report.probes (workerRows C q₀ ports i m rs) =
      RAMBuckets.cost Report.probes rs + rs.length*((C i).params+2) := by
  induction rs generalizing m st with
  | nil => simp [workerRows,RAMBuckets.cost]
  | cons rep rs ih =>
    obtain ⟨_,_,s,hn,hv⟩ := h
    rw [workerRows,RAMBuckets.cost,RAMBuckets.cost,
      (active_effect (initial := initial) (phases := phases) ports i m rep hn (C := C)).2.2.1,
      ih s _ hv,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Total calls plus probes for one online phase, charged against the raw
worker calls and the native row expression's metadata reads. -/
theorem row_cost (ports : Ports w) (m : Memory w) (j : Fin q₀) (row : Directory.Row d w)
    (v : row.Valid C ports) :
    RAMBuckets.cost Report.probes (rowLog plan ports m j row) =
      RAMBuckets.cost Report.probes row.reports + row.reports.length*((C row.worker).params+2) +
        (plan.recipes j).2.reads + 3*arity C + (C row.worker).params + 26 := by
  have hp := workerRows_cost (initial := initial) (phases := phases) ports row.worker _ _ _ _ _ v.frame
  rw [rowLog, RAMBuckets.cost_append, RAMBuckets.cost_append,hp,preparation]
  simp only [RAMBuckets.cost, (calendar_effect plan ports m j).2.2.1,
    (recipe_effect plan ports j _ _).2.2.1, (launch_effect (C := C) (initial := initial) (phases := phases) ports _).2.2.1,
    (stop_effect (C := C) (initial := initial) (phases := phases) ports row.worker _).2.2.1]
  omega

private theorem workerRows_after (ports : Ports w) (i : Fin d) (pub : Fin (C i).params → Word w)
    (bound st : Word w) (m : Memory w) (rs : List (Report w))
    (h : ValidTrace C i ports pub bound st m rs) :
    after m (eventLog (workerRows C q₀ ports i m rs)) = after m (eventLog rs) := by
  induction rs generalizing m st with
  | nil => rfl
  | cons rep rs ih =>
    obtain ⟨_,_,s,hn,hv⟩ := h
    have he := (active_effect (initial := initial) (phases := phases) ports i m rep hn (C := C)).2.1
    simp only [workerRows,eventLog,List.flatMap_cons,after,List.foldl_append]
    change after (after m (activeReport C q₀ ports i m rep).events) _ = after (after m rep.events) _
    rw [he]
    exact ih s _ hv

/-- Actual linked reports have the same memory and next state as the
continuation supplied to the phase composition theorem. -/
theorem row_effect (ports : Ports w) (m : Memory w) (j : Fin q₀) (row : Directory.Row d w)
    (input : row.input = rowInput plan ports m j) (v : row.Valid C ports) (state : Word w) :
    after m (eventLog (rowLog plan ports m j row)) = post C q₀ ports row ∧
    endState (some state) (rowLog plan ports m j row) = some 0 := by
  let pre := calendarMemory (d := d) ports m j
  let s := LevelCalendar.header (calendar plan) ports.data m
  have hc : after m (calendarReport plan ports m j).events = pre := (calendar_effect plan ports m j).2.1
  have hr : after pre (recipeReport plan ports j s pre).events = row.input :=
    (recipe_effect plan ports j s pre).2.1.trans input.symm
  have hl := (launch_effect (C := C) (initial := initial) (phases := phases) ports row.input).2.1
  have hw := workerRows_after (initial := initial) (phases := phases) ports row.worker _ _ _ _ _ v.frame
  have hs := stop_effect (C := C) (initial := initial) (phases := phases) ports row.worker (row.endMemory C ports)
  constructor
  · simp only [rowLog,preparation,eventLog,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,after,List.foldl_append]
    change after (after (after (after (after m (calendarReport plan ports m j).events)
      (recipeReport plan ports j s pre).events) (launchReport C q₀ ports (rowInput plan ports m j)).events)
      (eventLog (workerRows C q₀ ports row.worker (row.dataMemory C ports) row.reports)))
      (stopReport C q₀ ports row.worker (row.endMemory C ports)).events = _
    rw [hc,hr,← input,hl]
    change after (after (row.dataMemory C ports) (eventLog (workerRows C q₀ ports row.worker _ row.reports))) _ = _
    rw [hw]
    exact hs.2.1
  · rw [rowLog,endState_append]; exact hs.1

private theorem stored_field {m : Memory w} {base : Word w} {xs : List (Word w)}
    (h : Greedy.Stores m base xs) (i : Fin xs.length) : m (base+(i.val : Word w)).val = xs[i.val] := by
  induction xs generalizing base with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    cases i using Fin.cases with
    | zero => simpa using h.1
    | succ i =>
      simpa only [Fin.val_succ,Nat.cast_add,Nat.cast_one,add_assoc,add_comm (1 : Word w) (i.val : Word w),
        List.getElem_cons_succ] using ih h.2 i

/-- From a recipe's actual destination and field values, the launcher
installs the computed start, stop and parameters. Address separation
protects the row and the two controller counters through the tag transfer. -/
theorem computed_ready (ports : Ports w) (m : Memory w) (j : Fin q₀) (i : Fin d)
    (st stop : Word w) (params : Fin (arity C) → Word w) (frame : Directory.FrameFits C ports)
    (ordTag : ports.ordinal ≠ ports.tag) (totalTag : ports.rows ≠ ports.tag)
    (dest : let pre := calendarMemory (d := d) ports m j
      (plan.recipes j).2.address ports.data (LevelCalendar.header (calendar plan) ports.data m) pre =
        Directory.rowBase C ports pre)
    (fields : let pre := calendarMemory (d := d) ports m j
      (plan.recipes j).2.words ports.data (LevelCalendar.header (calendar plan) ports.data m) pre =
        LiveStageLink.tagWord w i.succ :: st :: stop :: List.ofFn params)
    (room : (Directory.rowBase C ports m).val + (arity C+3) ≤ 2^w)
    (away : ∀ addr ∈ [ports.tag,ports.ordinal,ports.rows], addr.val < (Directory.rowBase C ports m).val ∨
      (Directory.rowBase C ports m).val + (arity C+3) ≤ addr.val) :
    let input := rowInput plan ports m j
    input ports.ordinal.val = m ports.ordinal.val ∧ input ports.rows.val = m ports.rows.val ∧
    Directory.start C ports input = st ∧
    Ready C i ports (fun u ↦ params (Fin.castLE (params_le_arity C i) u)) stop (Directory.prepared C ports input) := by
  let base := Directory.rowBase C ports m
  let pre := calendarMemory (d := d) ports m j
  let xs := LiveStageLink.tagWord w i.succ :: st :: stop :: List.ofFn params
  let data := Greedy.writeRow pre base xs
  let input := rowInput plan ports m j
  have hord : pre ports.ordinal.val = m ports.ordinal.val := by
    simp [pre,calendarMemory,writeMemory,Fin.val_ne_of_ne ordTag]
  have hcount : pre ports.rows.val = m ports.rows.val := by
    simp [pre,calendarMemory,writeMemory,Fin.val_ne_of_ne totalTag]
  have same {mem : Memory w} (he : mem ports.ordinal.val = m ports.ordinal.val) :
      Directory.rowBase C ports mem = base := by
    change ports.directory + mem ports.ordinal.val * _ = ports.directory + m ports.ordinal.val * _
    rw [he]
  have hd : input = writeMemory data ports.tag 0 := by
    dsimp only [input,rowInput,data,pre,xs]
    rw [dest,fields,same hord]
  have hlen : xs.length = arity C+3 := by simp [xs]
  have fit : base.val + xs.length ≤ 2^w := hlen ▸ room
  have keep (a : Word w) (ha : a ∈ [ports.tag,ports.ordinal,ports.rows]) :
      data a.val = pre a.val :=
    Greedy.writeRow_outside pre base xs a.val fit (hlen ▸ away a ha)
  have hiord : input ports.ordinal.val = m ports.ordinal.val := by
    rw [hd,writeMemory,ite_eq_right (Fin.val_ne_of_ne ordTag),keep _ (by simp),hord]
  have hitot : input ports.rows.val = m ports.rows.val := by
    rw [hd,writeMemory,ite_eq_right (Fin.val_ne_of_ne totalTag),keep _ (by simp),hcount]
  have stores : Greedy.Stores data base xs := Greedy.writeRow_stores pre base xs fit
  have read (k : ℕ) (hk : k < xs.length) : input (base+(k : Word w)).val = xs[k] := by
    have hsum : (base+(k : Word w)).val = base.val+k := by
      rw [Fin.val_add,Fin.val_natCast,Nat.mod_eq_of_lt (by omega : k < 2^w),Nat.mod_eq_of_lt (by omega)]
    have ha := away ports.tag (by simp)
    change ports.tag.val < base.val ∨ base.val + (arity C+3) ≤ ports.tag.val at ha
    have hn : (base+(k : Word w)).val ≠ ports.tag.val := by rw [hsum]; omega
    rw [hd,writeMemory,ite_eq_right hn]
    exact stored_field stores ⟨k,hk⟩
  have hbase := same hiord
  have htag : input (Directory.rowBase C ports input).val = LiveStageLink.tagWord w i.succ := by
    rw [hbase]; simpa [xs] using read 0 (by omega)
  have hstart : Directory.start C ports input = st := by
    rw [Directory.start,hbase]; simpa [xs] using read 1 (by omega)
  have hstop : Directory.bound C ports input = stop := by
    rw [Directory.bound,hbase]; simpa [xs] using read 2 (by omega)
  have hp : Directory.words C ports i input = fun u ↦ params (Fin.castLE (params_le_arity C i) u) := by
    funext u
    have hu := u.isLt.trans_le (params_le_arity C i)
    change input ((Directory.rowBase C ports input + 2) + ((u.val+1 : ℕ) : Word w)).val = _
    rw [hbase, show (base+2)+((u.val+1 : ℕ) : Word w) = base+((u.val+3 : ℕ) : Word w) by push_cast; ring]
    have hk := read (u.val+3) (by omega)
    change input (base+((u.val+3 : ℕ) : Word w)).val =
      (LiveStageLink.tagWord w i.succ :: st :: stop :: List.ofFn params)[u.val.succ.succ.succ]'(by simp [hu]) at hk
    simp only [List.getElem_cons_succ,List.getElem_ofFn] at hk
    exact hk
  have hr := Directory.ready C ports input i frame htag
  rw [hp,hstop] at hr
  exact ⟨hiord,hitot,hstart,hr⟩

end CompressorRecords.Schedule.Online

end VPVNP
end Computability
end OAI
