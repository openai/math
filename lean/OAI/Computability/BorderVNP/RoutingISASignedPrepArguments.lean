import OAI.Computability.BorderVNP.RoutingISAScheduleClockArgumentVisits
import OAI.Computability.BorderVNP.RoutingISASignedPrepReportTail

/-! # Realization of the complete sparse argument builder on physical data -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM ScheduleClock CellDispatch CompactMachine DiagonalTallyCellReports

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- The supplemental splice, sparse exterior construction and typed serialization
all return on their actual chronological memory images. -/
theorem sparseCall_returns {s : Bank w} {m : Memory w} (src : SparseCallInput pub m) :
    Nonempty (Returns (.block [CellPacket.Supplement.Batch.entry,SparseExterior.prepare,TypedBatch.entry]) pub mac s m) := by
  let patched := CellPacket.Supplement.Batch.written m src.merge src.count
  obtain ⟨xs,u,first,_,_,_⟩ := CellPacket.Supplement.Batch.entry_run (pub := pub) (mac := mac) s m src.merge
    src.frame src.pointer src.length src.base src.indirect src.taskRoom src.controlRoom src.source src.apart
  obtain ⟨ys,v,mv,second,_,updated,_⟩ := SparseExterior.prepare_run (pub:=pub) (mac:=mac) u patched
    src.layout src.owned src.root src.loaded (src.root ▸ src.frame) src.header src.initial src.independent
  have equal : mv=src.compressed := funext fun i => Fin.ext (congrFun (updated.trans src.image.symm) i)
  subst mv
  obtain ⟨zs,z,last,_,_⟩ := TypedBatch.entry_run pub mac v src.compressed src.tasks src.typed.frame src.typed.width
    src.typed.base src.typed.length src.typed.space src.typed.allocated src.typed.stored src.typed.room
  exact ⟨⟨(_,_,_),first.seq (second.seq last)⟩⟩

/-- Actual fitted public inputs of the argument writers, at the post-report memory.
The first phase publishes the bucket directory. The task builder reads from its
return and writes the pure published memory used by the three final stages. -/
structure ArgumentInput (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) where
  /-- The real sparse rows and stable bucket on the post-report memory. -/
  fragments : FragmentDirectoryInput pub m
  /-- The native seven-word task directory and arena addresses. -/
  tasks : TypedTaskBuilder.Layout
  frame : (pub 0).val=tasks.frame
  fields : ∀ x : Returns (.seq FragmentRows.program FragmentBucket.program) pub mac s m, tasks.Fields (readings x.val.2.2)
  room : ∀ x : Returns (.seq FragmentRows.program FragmentBucket.program) pub mac s m, tasks.Room (readings x.val.2.2) w
  /-- Supplemental and compressed task inputs on the published builder memory. -/
  sparse : ∀ x : Returns (.seq FragmentRows.program FragmentBucket.program) pub mac s m, ∀ result : Memory w,
    readings result=tasks.published (readings x.val.2.2) → SparseCallInput pub result

/-- The native code, including the six sparse fragments, supplies the entire
serializer return from its actual numeric and memory conditions. -/
theorem arguments_returns {s : Bank w} {m : Memory w} (src : ArgumentInput pub mac s m) :
    Nonempty (Returns arguments pub mac s m) := by
  let fr := src.fragments
  obtain ⟨a,v,mv,ra,_,_⟩ := fragmentDirectory_run pub mac s m fr.layout fr.bucket fr.control fr.loaded fr.fit
    fr.base fr.rows fr.cells fr.room fr.header fr.frame fr.controlRoom
  let first : Returns (.seq FragmentRows.program FragmentBucket.program) pub mac s m := ⟨(a,v,mv),ra⟩
  obtain ⟨b,z,mz,rb,_,im⟩ := TypedTaskBuilder.program_run pub mac v mv src.tasks src.frame (src.fields first) (src.room first)
  let second : Returns TypedTaskBuilder.program pub mac v mv := ⟨(b,z,mz),rb⟩
  obtain ⟨endRun⟩ := sparseCall_returns (s := z) (mac := mac) (src.sparse first mz im)
  exact ⟨argumentVisitsEquiv pub mac s m ⟨first,second,endRun⟩⟩

/-- On these physical allocations every report contributes exactly one preparation
return. The checked per-cell report fiber therefore needs no accepted-tail predicate. -/
noncomputable def fittedReportTailEquiv {s : Bank w} {m : Memory w} (d : Returns controls pub mac s m)
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor} {description : ℕ}
    (seed : PreparedReportInput pub d.val.2.2 cs q description)
    (fitted : ∀ rows : ReportAssignments cs, let r := assignedReportReturnEquiv seed mac d.val.2.1 rows
      ArgumentInput pub mac r.val.2.1 r.val.2.2) :
    LocalTail pub mac s m ≃ ReportAssignments cs :=
  allReportTailEquiv pub mac d seed fun rows => arguments_returns (fitted rows)

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
