import OAI.Computability.VPVNP.CompressorOnlinePeel
import OAI.Computability.VPVNP.CompressorOnlineWorkerSegment

/-! # Recovering a physical descriptor row on an accepting run

The calendar, recipe, launcher, data worker and closing call are inverted on
the same choice stream. Only the worker uses private choice bits. Its local
invariant supplies the valid frame, live cursor, and private clock for every
successful call, including calls reached by arbitrary submitted tapes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Schedule.Online.Run

open BurstRAM

variable {d initial phases w : ℕ} {C : Catalog d} (plan : Config C initial phases) (ports : Ports w)
local notation "q₀" => initial+phases
local notation "D₀" => N d q₀

/-- All data needed to enter a source row in the current physical memory.
The invariant and its advancement rule concern one data call at a time. -/
structure RowStart (cap : ℕ) (m : Memory w) where
  /-- Calendar phase selected for the current row ordinal at entry to the inverse run. -/
  phase : Fin q₀
  /-- Catalog index of the data worker launched for this row. -/
  worker : Fin d
  /-- Private fuel bound available to each data-worker call while recovering the row. -/
  fuel : ℕ
  /-- Predicate on the worker cursor and memory used to validate successive calls within the
  row. -/
  invariant : Word w → Memory w → Prop
  calendarPhase : (calendar plan).phase (m ports.ordinal.val).val = phase.val
  liveRow : rowInput plan ports m phase ports.ordinal.val < rowInput plan ports m phase ports.rows.val
  positiveFuel : 0 < fuel
  recipeCap : (plan.recipes phase).2.code.length+1+2*D₀+5 ≤ cap
  dataCap : fuel+3+4*((C worker).params+1)+2*D₀+5 ≤ cap
  ready : let entry := rowInput plan ports m phase
    Ready C worker ports (Directory.words C ports worker entry) (Directory.bound C ports entry)
      (Directory.prepared C ports entry)
  initialInv : let entry := rowInput plan ports m phase
    invariant (Directory.start C ports entry) (Directory.prepared C ports entry)
  dataStep : let entry := rowInput plan ports m phase
    WorkerStep ports worker (Directory.words C ports worker entry) (Directory.bound C ports entry) cap fuel invariant

/-- Separate the complete first row and accepting remainder. The witness is
built from the supplied stream's actual reports, and its data execution is
validated at the row-specific private clock. -/
theorem recover_row {m : Memory w} {state : Word w} {cap : ℕ} (entry : RowStart plan ports cap m)
    (htag : m ports.tag.val = LiveStageLink.tagWord w (calendarIndex d q₀)) (fits : D₀ ≤ 2^w)
    (active : m ports.ordinal.val < m ports.rows.val)
    (calCap : 30+2*q₀+2*D₀+5 ≤ cap) (launchCap : 20+6*(arity C+1)+2*D₀+5 ≤ cap)
    {bits : List (List Bool)} {logs : List (Report w)}
    (run : runSegment (program plan ports) cap (some state) m bits = some logs) (halt : endState (some state) logs = none) :
    ∃ (s : Step d q₀ w), ∃ tail more, s.Valid plan ports cap m ∧ s.phase = entry.phase ∧
      s.row.worker = entry.worker ∧ s.row.fuel = entry.fuel ∧
      bits = rowChoices s.row ++ tail ∧ logs = rowLog plan ports m s.phase s.row ++ more ∧
      runSegment (program plan ports) cap (some 0) (post C q₀ ports s.row) tail = some more ∧
      endState (some 0) more = none := by
  let x := rowInput plan ports m entry.phase
  obtain ⟨rest,reps,hbits,hlogs,run',halt'⟩ := recover_preparation plan ports htag fits active entry.calendarPhase
    entry.liveRow calCap entry.recipeCap launchCap run halt
  obtain ⟨data,tail,raw,more,hdata,hrep,source,valid,hr,hh⟩ :=
    recover_worker_segment plan ports entry.worker (Directory.words C ports entry.worker x) (Directory.bound C ports x)
      cap entry.fuel entry.invariant entry.dataStep fits _ _ rest reps entry.ready entry.initialInv run' halt'
  let s : Step d q₀ w := ⟨entry.phase, ⟨x, entry.worker, entry.fuel, data, raw⟩⟩
  have hv : s.Valid plan ports cap m := ⟨entry.calendarPhase,active,rfl,
    ⟨by simp [s, x, rowInput, writeMemory],entry.liveRow,entry.positiveFuel,source,valid⟩,entry.recipeCap,entry.dataCap⟩
  refine ⟨s,tail,more,hv,rfl,rfl,rfl,?_,?_,hr,hh⟩
  · rw [hbits,hdata]; simp [s,rowChoices,List.append_assoc]
  · rw [hlogs,hrep]; simp [s,x,rowLog,Directory.Row.endMemory,Directory.Row.dataMemory,List.append_assoc]

end CompressorRecords.Schedule.Online.Run

end VPVNP
end Computability
end OAI
