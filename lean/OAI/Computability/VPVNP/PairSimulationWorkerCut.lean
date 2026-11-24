import OAI.Computability.VPVNP.PairSimulationSelectorRow
import OAI.Computability.VPVNP.CompressorOnlineOrdinalForward
import OAI.Computability.VPVNP.CompressorOnlineBranchCut

/-! # The native term-worker cut at a physical calendar boundary

Build every branch's source row from its encoded tapes and the actual
reports returned by the term worker. The same boundary certificate
recovers arbitrary accepting streams. The successor memory contains the
records written by the recovered term.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open Compression CompressorRecords CompressorRecords.SelectedTerms NetworkKernel BurstRAM
open CompressorRecords.Schedule CompressorRecords.Schedule.Online
open scoped Fin.CommRing

variable {k : Type*} [Field k] {S : BlockSchedule k} {B : S.Templates}
  {A : Type*} [CommRing A] {f : B.Entry → A} {hf : B.IsSolution f}
  {a g b n w : ℕ} {X : State a g} {p : StatePass A X b n} {o : PassOrigin B f hf p}
  {d initial phases cap : ℕ} {C : Catalog d} {plan : Config C initial phases} {ports : Ports w} {m : Memory w}

/-- Instantiate the catalog worker named at the current calendar row with the directory words
computed from that row's phase and memory. -/
def RowStartTable (entry : Run.RowStart plan ports cap m) : ProgramTable w :=
  let x := rowInput plan ports m entry.phase
  ⟨_,((C entry.worker).table.instantiate w (Directory.words C ports entry.worker x)).program⟩

/-- Calendar step for a semantic term choice, recording the entry phase, worker and fuel
together with the per-motif worker tapes and reports from the selected run. -/
noncomputable def WorkerInput.selectedStep (I : WorkerInput o w) (entry : Run.RowStart plan ports cap m)
    (i : p.step.Choice) : Run.Step d (initial+phases) w :=
  ⟨entry.phase,⟨rowInput plan ports m entry.phase,entry.worker,entry.fuel,List.ofFn (workerTapes o w i),(I.selected_run i).choose⟩⟩

theorem WorkerInput.selectedStep_valid (I : WorkerInput o w) (entry : Run.RowStart plan ports cap m)
    (live : m ports.ordinal.val < m ports.rows.val) (installed : RowStartTable entry = I.table)
    (fuel : entry.fuel = I.fuel) (start : Directory.start C ports (rowInput plan ports m entry.phase) = 0)
    (stop : (Directory.bound C ports (rowInput plan ports m entry.phase)).val = o.motifCount)
    (memory : Directory.prepared C ports (rowInput plan ports m entry.phase) = I.memory) (i : p.step.Choice) :
    (I.selectedStep entry i).Valid plan ports cap m := by
  let G := grid o
  let x := rowInput plan ports m entry.phase
  let st := Directory.start C ports x
  let bound := Directory.bound C ports x
  let pub := Directory.words C ports entry.worker x
  let bank := Directory.prepared C ports x
  let cursor (j : ℕ) : Word w := j
  let tapes := List.ofFn (workerTapes o w i)
  let logs := (I.selected_run i).choose
  have hrun := (I.selected_run i).choose_spec.1
  have run : runSegment (RowStartTable entry).2 entry.fuel (some st) bank tapes = some logs := by
    have h := congrArg (fun T : ProgramTable w => runSegment T.2 I.fuel (some 0) I.memory tapes) installed
    change st = 0 at start
    change bank = I.memory at memory
    rw [fuel,start,memory]
    exact h.trans hrun
  refine ⟨entry.calendarPhase,live,rfl,⟨by simp [selectedStep,rowInput,writeMemory],
    entry.liveRow,entry.positiveFuel,run,?_⟩,entry.recipeCap,entry.dataCap⟩
  have hfit : o.motifCount < 2^w := stop ▸ bound.isLt
  have ha (j : ℕ) (hj : j<o.motifCount) : cursor j < bound := by
    change j%(2^w)<bound.val
    rw [Nat.mod_eq_of_lt (hj.trans hfit),stop]
    exact hj
  have hc : bound ≤ cursor o.motifCount := by
    change bound.val ≤ o.motifCount%(2^w)
    rw [Nat.mod_eq_of_lt hfit,stop]
  have advance (j : ℕ) (hj : j<o.motifCount) (mem : Memory w) (b : List Bool) (rep : Report w)
      (h : execute (RowStartTable entry).2 entry.fuel ((RowStartTable entry).2.start (cursor j)) mem b = some rep) :
      rep.result = some (cursor (j+1)) := by
    have hsame := congrArg (fun T : ProgramTable w => execute T.2 entry.fuel (T.2.start (cursor j)) mem b) installed
    have native := hsame.symm.trans h
    let a : Fin o.motifCount := ⟨j,hj⟩
    obtain ⟨hs,ht⟩ := I.addresses a
    have hsrc := hs.symm ▸ I.layout.sourceFits a
    have hdst := ht.symm ▸ I.layout.termFits a
    have inc := (TermWorker.Footprint.call G.block G.demandOrder.entries G.supplyOrder.entries I.addr
      (cursor j) mem entry.fuel b rep hsrc hdst native).1
    simpa only [cursor,Nat.cast_add,Nat.cast_one] using inc
  have enough : entry.fuel ≤ cap := by have h := entry.dataCap; omega
  change ValidTrace C entry.worker ports pub bound st bank logs
  have inv := entry.initialInv
  change entry.invariant st bank at inv
  change st = 0 at start
  rw [start] at run inv ⊢
  exact ordinalFrame entry.dataStep enough cursor ha hc advance 0 tapes bank logs
    (by simp [tapes]) entry.ready inv run

/-- Every semantic term has one actual native row and every accepting
continuation of the table contains one of these full row prefixes. -/
noncomputable def WorkerInput.selectorCut (I : WorkerInput o w) (entry : Run.RowStart plan ports cap m)
    (controls : Run.ControlBounds plan cap (w := w)) (state : Word w)
    (tag : m ports.tag.val = LiveStageLink.tagWord w (calendarIndex d (initial+phases)))
    (live : m ports.ordinal.val < m ports.rows.val) (installed : RowStartTable entry = I.table)
    (fuel : entry.fuel = I.fuel) (start : Directory.start C ports (rowInput plan ports m entry.phase) = 0)
    (stop : (Directory.bound C ports (rowInput plan ports m entry.phase)).val = o.motifCount)
    (memory : Directory.prepared C ports (rowInput plan ports m entry.phase) = I.memory) :
    BranchSegments.Cut (program plan ports) cap (some state) m p.step.Choice := by
  apply Run.selectorCut plan ports controls tag entry live (I.selectedStep entry)
    (I.selectedStep_valid entry live installed fuel start stop memory) ?_ o.motifCount ?_ ?_
  · intro s valid hp hw hf
    have x := valid.input.trans (congrArg (rowInput plan ports m) hp)
    have same : sourceTable C ports s.row = I.table := by
      let installedAt (j : Fin d) : ProgramTable w :=
        ⟨_,((C j).table.instantiate w (Directory.words C ports j (rowInput plan ports m entry.phase))).program⟩
      have eq := (congrArg installedAt hw).trans installed
      simpa only [sourceTable,x] using eq
    obtain ⟨_,i,hi,_⟩ := I.validRow_unique s.row valid.source same (hf.trans fuel)
      (x ▸ start) (x ▸ stop) (by simpa only [Directory.Row.dataMemory,x] using memory)
    exact ⟨i,hi⟩
  · exact fun _ => List.length_ofFn
  · intro i j h
    exact I.termEquiv.injective (Subtype.ext (List.ofFn_inj.mp h))

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
