import OAI.Computability.VPVNP.CompressorBranchSegments

/-! # Native branch cuts of the fixed online descriptor table

The data bursts of a term row occur between three empty entering control
calls and one empty returning call. Every valid source tape selects a term,
and all terms use the same number of motifs. These facts distinguish the
terms even in the presence of arbitrary later native calls. The ordinary
descriptor rows are executed from the memory produced by each preceding row.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Schedule.Online.Run

open BurstRAM BranchSegments

variable {w d initial phases : ℕ} {C : Catalog d} (plan : Config C initial phases) (ports : Ports w)
local notation "q" => initial + phases
local notation "D" => N d q
local notation "prog" => program plan ports
local notation "tag" => LiveStageLink.tagWord w (calendarIndex d q)

/-- All non-data instruction bounds are fixed by the finite program. -/
structure ControlBounds (_plan : Config C initial phases) (cap : ℕ) : Prop where
  tags : D ≤ 2^w
  calendar : 30+2*q+2*D+5 ≤ cap
  launch : 20+6*(arity C+1)+2*D+5 ≤ cap

variable {cap : ℕ} {m : Memory w} {state : Word w}

/-- The actual online portion for a single valid source row. -/
def oneRow (bounds : ControlBounds plan cap (w := w)) (htag : m ports.tag.val = tag)
    (s : Step d q w) (h : s.Valid plan ports cap m) : Segment prog cap (some state) m where
  bits := rowChoices s.row
  logs := rowLog plan ports m s.phase s.row
  run := by
    have run := row_segment plan ports state m s.phase s.row h.input h.source htag bounds.tags h.active h.phase
      bounds.calendar h.recipeCap bounds.launch h.dataCap []
    simpa only [List.append_nil,runSegment,Option.map_some] using run

theorem oneRow_state (bounds : ControlBounds plan cap (w := w)) (htag : m ports.tag.val = tag)
    (s : Step d q w) (h : s.Valid plan ports cap m) :
    (oneRow plan ports (state := state) bounds htag s h).state = some 0 :=
  (row_effect plan ports m s.phase s.row h.input h.source state).2

theorem oneRow_memory (bounds : ControlBounds plan cap (w := w)) (htag : m ports.tag.val = tag)
    (s : Step d q w) (h : s.Valid plan ports cap m) :
    (oneRow plan ports (state := state) bounds htag s h).memory = post C q ports s.row :=
  (row_effect plan ports m s.phase s.row h.input h.source state).1

/-- A finite interval of valid native rows, ending at a calendar boundary.
The ending ordinal may still have further phases to execute. -/
def Interval (cap : ℕ) : Memory w → List (Step d q w) → Prop
  | _, [] => True
  | m, s :: rest => s.Valid plan ports cap m ∧ Interval cap (post C q ports s.row) rest

/-- Concatenate the choice tapes of the successive rows in an online interval. -/
def intervalBits (steps : List (Step d q w)) := steps.flatMap fun s => rowChoices s.row

/-- Replay the interval's row reports in chronological order using the memory produced by each
preceding row. -/
def intervalLog : Memory w → List (Step d q w) → List (Report w)
  | _, [] => []
  | m, s :: rest => rowLog plan ports m s.phase s.row ++ intervalLog (post C q ports s.row) rest

/-- Physical segment witnessing a valid interval of online rows with its original choice tapes
and report log. -/
def intervalSegment (bounds : ControlBounds plan cap (w := w)) (htag : m ports.tag.val = tag)
    (steps : List (Step d q w)) (h : Interval plan ports cap m steps) : Segment prog cap (some state) m where
  bits := intervalBits steps
  logs := intervalLog plan ports m steps
  run := by
    induction steps generalizing state m with
    | nil => rfl
    | cons s rest ih =>
      change runSegment _ _ _ _ (rowChoices s.row ++ intervalBits rest) = _
      rw [row_segment plan ports state m s.phase s.row h.1.input h.1.source htag bounds.tags h.1.active h.1.phase
        bounds.calendar h.1.recipeCap bounds.launch h.1.dataCap]
      rw [ih (state := 0) (by simp [post,writeMemory]) h.2]
      rfl

theorem interval_memory (bounds : ControlBounds plan cap (w := w)) (htag : m ports.tag.val = tag)
    (steps : List (Step d q w)) (h : Interval plan ports cap m steps) :
    (intervalSegment plan ports (state := state) bounds htag steps h).memory =
      finalMemory (C := C) ports m steps := by
  change after m (eventLog (intervalLog plan ports m steps)) = _
  induction steps generalizing m with
  | nil => rfl
  | cons s rest ih =>
    rw [intervalLog,SourceWalk.after_append,(row_effect plan ports m s.phase s.row h.1.input h.1.source state).1]
    exact ih (by simp [post,writeMemory]) h.2

theorem interval_state_zero (bounds : ControlBounds plan cap (w := w)) (htag : m ports.tag.val = tag)
    (steps : List (Step d q w)) (h : Interval plan ports cap m steps) :
    (intervalSegment plan ports (state := 0) bounds htag steps h).state = some 0 := by
  change endState (some 0) (intervalLog plan ports m steps) = _
  induction steps generalizing m with
  | nil => rfl
  | cons s rest ih =>
    rw [intervalLog,endState_append,(row_effect plan ports m s.phase s.row h.1.input h.1.source 0).2]
    exact ih (by simp [post,writeMemory]) h.2

/-- The entire native interval, including each row's control calls, uses
empty tapes whenever every scheduled source burst does. -/
theorem quietInterval (steps : List (Step d q w))
    (quiet : ∀ s ∈ steps, s.row.choices = List.replicate s.row.choices.length []) :
    intervalBits steps = List.replicate (intervalBits steps).length [] := by
  induction steps with
  | nil => rfl
  | cons s rest ih =>
    have eq := quiet s List.mem_cons_self
    have tail := ih (fun r hr => quiet r (List.mem_cons_of_mem _ hr))
    change rowChoices s.row ++ intervalBits rest = List.replicate (rowChoices s.row ++ intervalBits rest).length []
    rw [List.length_append,List.replicate_add]
    have hr : rowChoices s.row = List.replicate (rowChoices s.row).length [] := by
      change [] :: [] :: [] :: (s.row.choices ++ [[]]) = _
      simp only [rowChoices,List.length_cons,List.length_append,List.replicate_succ]
      rw [List.replicate_add,← eq]
      rfl
    exact congrArg₂ List.append hr tail

variable {I : Type*}

/-- Invert a term row, using its actual one-call worker invariant and the
source selector's completeness on valid recovered rows. -/
def selectorCut (bounds : ControlBounds plan cap (w := w)) (htag : m ports.tag.val = tag)
    (entry : RowStart plan ports cap m) (active : m ports.ordinal.val < m ports.rows.val)
    (rows : I → Step d q w) (valid : ∀ i, (rows i).Valid plan ports cap m)
    (decode : ∀ s : Step d q w, s.Valid plan ports cap m → s.phase = entry.phase →
      s.row.worker = entry.worker → s.row.fuel = entry.fuel →
      ∃ i, s.row.choices = (rows i).row.choices)
    (count : ℕ) (lengths : ∀ i, (rows i).row.choices.length = count)
    (unique : Function.Injective fun i => (rows i).row.choices) :
    Cut prog cap (some state) m I where
  part i := oneRow plan ports bounds htag (rows i) (valid i)
  separate i j a b h := by
    change rowChoices (rows i).row ++ a = rowChoices (rows j).row ++ b at h
    simp only [rowChoices,List.cons_append,List.cons.injEq,true_and,List.append_assoc] at h
    have e := congrArg (List.take count) h
    have hi := lengths i
    have hj := lengths j
    apply unique
    rw [← hi,List.take_left,hi,← hj,List.take_left] at e
    exact e
  cover bs rs run halt := by
    obtain ⟨s,tail,more,h,hp,hw,hf,hb,_,_,_⟩ :=
      recover_row plan ports entry htag bounds.tags active bounds.calendar bounds.launch run halt
    obtain ⟨i,selected⟩ := decode s h hp hw hf
    exact ⟨i,tail,by simpa only [oneRow,rowChoices,selected] using hb⟩

end CompressorRecords.Schedule.Online.Run

end VPVNP
end Computability
end OAI
