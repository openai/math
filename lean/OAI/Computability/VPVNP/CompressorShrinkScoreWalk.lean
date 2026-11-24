import OAI.Computability.VPVNP.CompressorShrinkSelectedPlan
import OAI.Computability.VPVNP.CompressorSourceWalk

/-! # The ten selected-score visits as a chronological native walk

The one-shot calendar programs return cursor one. Their memory operations
coincide with the clear and comparison operations in the score calculation.
The eight strided scans use exactly the original reports.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ScorePackets

open BurstRAM BlockPlanner PhaseRecipe TermScores

/-- A stage of layout scoring clears both accumulators, scans one of the eight layout-and-role
coordinates, or compares the totals to choose a layout. -/
inductive Stage where
  | clear
  | axis (j : Fin 8)
  | compare

/-- Score stages in execution order, clearing the accumulators once, scanning coordinates zero
through seven, then comparing the two layout scores. -/
def stages : List Stage := [.clear] ++ List.ofFn Stage.axis ++ [.compare]
/-- The planner visit implementing a score stage on the selected plan’s term and accumulator
tables. -/
def Stage.visit (I : SelectedPlan.Inputs) : Stage → Visit
  | .clear => SelectedPlan.clear I
  | .axis j => SelectedPlan.axis I j
  | .compare => SelectedPlan.compare I

/-- The ten score visits obtained by translating the ordered score stages into planner visits
for the supplied inputs. -/
def visits (I : SelectedPlan.Inputs) := stages.map (Stage.visit I)

theorem visits_eq (I : SelectedPlan.Inputs) :
    visits I = [SelectedPlan.clear I] ++ List.ofFn (SelectedPlan.axis I) ++ [SelectedPlan.compare I] := by
  simp [visits,stages,Stage.visit]

theorem length : stages.length = 10 := by simp [stages]

variable {w : ℕ} (T : Tables w) (n : ℕ)

/-- Give a one-shot score report the calendar’s return cursor of one while retaining its event
trace. -/
def advance (r : Report w) : Report w := ⟨r.events,some 1⟩

/-- Specifies a stage’s source reports. An axis executes its score worker once per motif with
empty choices, while clearing and comparison each produce one report returning cursor one. -/
def Native : Stage → Memory w → List (Report w) → Prop
  | .clear,_,rs => rs = [advance (clearReport T)]
  | .axis j,m,rs => runSegment (workerMachine T (SelectedScore.axes j)).program 27 (some 0) m
      (List.replicate n []) = some rs
  | .compare,m,rs => rs = [advance (compareReport T m)]

private theorem axis_walk (js : List (Fin 8)) (mem : Memory w) (rs : List (Report w))
    (hr : runAxes T n (js.map SelectedScore.axes) mem = some rs) :
    SourceWalk (Native T n) (js.map Stage.axis) mem rs := by
  induction js generalizing mem rs with
  | nil =>
    have e : [] = rs := Option.some.inj hr
    subst rs
    exact .done mem
  | cons j js ih =>
    simp only [List.map_cons,runAxes] at hr
    cases hp : runSegment (workerMachine T (SelectedScore.axes j)).program 27 (some 0) mem
        (List.replicate n []) with
    | none => simp [hp] at hr
    | some head =>
      cases ht : runAxes T n (js.map SelectedScore.axes) (after mem (eventLog head)) with
      | none => simp [hp,ht] at hr
      | some tail =>
        simp [hp,ht] at hr
        subst rs
        exact .next hp (ih _ _ ht)

/-- Decompose the actual native score calculation into its ten recipe
occurrences, retaining every event and the complete post-memory. -/
theorem walk (mem : Memory w) (rs : List (Report w))
    (hr : run T n (List.ofFn SelectedScore.axes) mem = some rs) :
    ∃ logs, SourceWalk (Native T n) stages mem logs ∧ eventLog logs = eventLog rs := by
  let c := clearReport T
  let mc := after mem c.events
  rw [run,execute_clear] at hr
  change (runAxes T n (List.ofFn SelectedScore.axes) mc).bind _ = _ at hr
  cases ha : runAxes T n (List.ofFn SelectedScore.axes) mc with
  | none => rw [ha] at hr; cases hr
  | some middle =>
    let last := after mc (eventLog middle)
    rw [ha] at hr
    change (execute (compareMachine T).program 10 ((compareMachine T).program.start 0) last []).bind _ = _ at hr
    rw [execute_compare] at hr
    have e : c :: (middle ++ [compareReport T last]) = rs := Option.some.inj hr
    subst rs
    have ha' := axis_walk T n (List.ofFn id) mc middle (by simpa only [List.map_ofFn,Function.comp_id] using ha)
    have hw : SourceWalk (Native T n) (List.ofFn Stage.axis) mc middle := by
      simpa only [List.map_ofFn,Function.comp_id] using ha'
    have hlast : SourceWalk (Native T n) [.compare] last [advance (compareReport T last)] :=
      SourceWalk.singleton (i := Stage.compare) rfl
    refine ⟨advance c :: (middle ++ [advance (compareReport T last)]),?_,?_⟩
    · change SourceWalk (Native T n) (.clear :: (List.ofFn Stage.axis ++ [.compare])) mem
        ([advance c] ++ (middle ++ [advance (compareReport T last)]))
      exact .next (show Native T n .clear mem [advance c] from rfl) (hw.append hlast)
    · simp [eventLog,advance]

end CompressorRecords.ScorePackets

end

end VPVNP
end Computability
end OAI
