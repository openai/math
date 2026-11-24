import OAI.Computability.VPVNP.CompressorRecordsOnlineRun
import OAI.Computability.VPVNP.LiveDeterministicPaths

/-! # Recovering online calendar boundaries from arbitrary native branch tapes

An accepting run must perform the calendar lookup, the selected row recipe
and the launch before it can execute data calls. At the end of the schedule
there is exactly one empty terminal call. These facts apply to arbitrary
supplied choice streams, including streams with extra or missing bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Schedule.Online

open BurstRAM

variable {d initial phases w : ℕ} {C : Catalog d} (plan : Config C initial phases) (ports : Ports w)
local notation "q₀" => initial+phases
local notation "D₀" => N d q₀

/-- The three preparation reports leave the physical memory and persistent
word specified by the dynamically selected directory row. -/
theorem preparation_effect (state : Word w) (m : Memory w) (j : Fin q₀) :
    endState (some state) (preparation plan ports m j) = some (Directory.start C ports (rowInput plan ports m j)) ∧
    after m (eventLog (preparation plan ports m j)) = Directory.prepared C ports (rowInput plan ports m j) := by
  let pre := calendarMemory (d := d) ports m j
  let s := LevelCalendar.header (calendar plan) ports.data m
  have h₁ := (calendar_effect plan ports m j).2.1
  have h₂ := (recipe_effect plan ports j s pre).2.1
  have h₃ := launch_effect (C := C) (initial := initial) (phases := phases) ports (rowInput plan ports m j)
  constructor
  · exact h₃.1
  · simp only [preparation, eventLog, List.flatMap_cons, List.flatMap_nil, List.append_nil, after, List.foldl_append]
    change after (after (after m (calendarReport plan ports m j).events) (recipeReport plan ports j s pre).events)
      (launchReport C q₀ ports (rowInput plan ports m j)).events = _
    rw [show after m (calendarReport plan ports m j).events = pre from h₁,
      show after pre (recipeReport plan ports j s pre).events = rowInput plan ports m j from h₂]
    exact h₃.2.1

/-- The entire deterministic prefix is forced even for a malformed candidate
stream. The suffix starts at the physical worker and is itself accepting. -/
theorem recover_preparation {state : Word w} {m : Memory w} {j : Fin q₀} {cap : ℕ}
    (htag : m ports.tag.val = LiveStageLink.tagWord w (calendarIndex d q₀)) (fits : D₀ ≤ 2^w)
    (active : m ports.ordinal.val < m ports.rows.val) (hj : (calendar plan).phase (m ports.ordinal.val).val = j.val)
    (activeRow : rowInput plan ports m j ports.ordinal.val < rowInput plan ports m j ports.rows.val)
    (calCap : 30+2*q₀+2*D₀+5 ≤ cap) (recipeCap : (plan.recipes j).2.code.length+1+2*D₀+5 ≤ cap)
    (launchCap : 20+6*(arity C+1)+2*D₀+5 ≤ cap)
    {bits : List (List Bool)} {logs : List (Report w)}
    (run : runSegment (program plan ports) cap (some state) m bits = some logs) (halt : endState (some state) logs = none) :
    let row := rowInput plan ports m j
    ∃ tail reps, bits = [] :: [] :: [] :: tail ∧ logs = preparation plan ports m j ++ reps ∧
      runSegment (program plan ports) cap (some (Directory.start C ports row)) (Directory.prepared C ports row) tail = some reps ∧
      endState (some (Directory.start C ports row)) reps = none := by
  intro row
  have hp : runSegment (program plan ports) cap (some state) m (List.replicate 3 []) = some (preparation plan ports m j) := by
    change runSegment _ _ _ _ ([] :: [] :: [] :: []) = _
    rw [prepare_segment plan ports state m j htag fits active hj activeRow calCap recipeCap launchCap []]
    simp [runSegment]
  obtain ⟨tail,reps,hbits,rfl,hrest⟩ := LiveProgram.split_empty_segment hp run halt
  obtain ⟨hs,hm⟩ := preparation_effect plan ports state m j
  rw [hs,hm] at hrest
  rw [endState_append,hs] at halt
  exact ⟨tail,reps,hbits,rfl,hrest,halt⟩

/-- Once the ordinal reaches the exclusive row bound, every accepting native
execution consists solely of the empty-choice calendar halt. -/
theorem recover_terminal {state : Word w} {m : Memory w} {cap : ℕ}
    (htag : m ports.tag.val = LiveStageLink.tagWord w (calendarIndex d q₀)) (fits : D₀ ≤ 2^w)
    (stop : m ports.rows.val ≤ m ports.ordinal.val) (clock : 6+2*D₀+5 ≤ cap)
    {bits : List (List Bool)} {logs : List (Report w)}
    (run : runSegment (program plan ports) cap (some state) m bits = some logs) (halt : endState (some state) logs = none) :
    bits = [[]] ∧ logs = [linked ports (calendarIndex d q₀) (LevelCalendar.closedReport ports.data m)] := by
  let r := linked ports (calendarIndex d q₀) (LevelCalendar.closedReport ports.data m)
  have hr := calendar_stop plan ports state m htag fits stop clock
  have hp : runSegment (program plan ports) cap (some state) m (List.replicate 1 []) = some [r] := by
    simp [runSegment, hr, r]
  obtain ⟨tail,reps,hbits,hlogs,hrest⟩ := LiveProgram.split_empty_segment hp run halt
  have hc : endState (some state) [r] = none := (terminal_effect (initial := initial) (phases := phases) (d := d) ports m).1
  rw [hc] at hrest
  cases tail with
  | nil =>
    change some [] = some reps at hrest
    cases Option.some.inj hrest
    exact ⟨hbits.trans (List.append_nil _), hlogs.trans (List.append_nil _)⟩
  | cons _ _ => contradiction

end CompressorRecords.Schedule.Online

end VPVNP
end Computability
end OAI
