import OAI.Computability.VPVNP.CompressorPassIntervalData
import OAI.Computability.VPVNP.CompressorScheduledTraceData

/-! # Joining the physical intervals of one shrinking or refresh pass

The deterministic preparation and completion can each contain many data
workers. Between them the native selecting row chooses the mathematical
term. The three actual inner report lists concatenate, at the same small
clock, and the final state and resident records belong to the selected
successor. Every partial physical run preserves the low-address frame.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.ScheduledTrace

open BurstRAM BranchSegments SourceBankFrame BlockPlanner Compression PassTimeline

variable {w cap small : ℕ} {Q : Type*} {P : BurstRAM.Program w Q} {st st' : Option (Word w)} {m : Memory w}
  {A : Script} {pub : Fin 11 → Word w} {I : Type*}

private def segmentAt (s : Segment P cap st m) (eq : st' = st) : Segment P cap st' m :=
  ⟨s.bits,s.logs,by rw [eq]; exact s.run⟩

private def cutAt (c : Cut P cap st m I) (eq : st' = st) : Cut P cap st' m I where
  part i := segmentAt (c.part i) eq
  separate i j a b e := c.separate i j a b e
  cover bs rs run halt := by rw [eq] at run halt; exact c.cover bs rs run halt

/-- Use the register state actually returned by a preceding interval,
leaving all tapes, reports, source costs and memories definitionally equal. -/
def QuietInterval.atState (s : QuietInterval A pub cap small st m) (eq : st' = st) :
    QuietInterval A pub cap small st' m where
  segment := segmentAt s.segment eq
  quiet := s.quiet
  stable := s.stable
  state := by change endState st' s.segment.logs = some 0; rw [eq]; exact s.state
  source := ⟨s.source.logs,by subst st'; exact s.source.run,s.source.frame⟩

/-- Transport a selector interval and its branch evidence to an equal initial state. -/
def SelectorInterval.atState (s : SelectorInterval A pub cap small st m I) (eq : st' = st) :
    SelectorInterval A pub cap small st' m I where
  cut := cutAt s.cut eq
  frame := ⟨s.frame.parts,fun bs rs run => s.frame.prefix bs rs (eq ▸ run)⟩
  state i := by change endState st' (s.cut.part i).logs = some 0; rw [eq]; exact s.state i
  source i := ⟨(s.source i).logs,by subst st'; exact (s.source i).run,(s.source i).frame⟩

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
  {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f} {resident : Resident B f hf w}
  {pitch : Word w} {total rate : ℕ} {loc : Located S.steps} {a g b n : ℕ} {X : State a g}
  {p : StatePass R X b n} {o : PassOrigin B f hf p} {encode : p.step.Choice → List Bool}
  {past : List (SelectedLevel B f hf)}
local notation "script" => BlockProgram.script B

/-- Assemble one mathematical pass from its actual before/selection/after
workspace intervals. The side conditions concern only the physical sums and
the data resident in the actual final memory of the completion interval. -/
def PassRun.ofIntervals (before : QuietInterval script pub cap small (some 0) m)
    (select : SelectorInterval script pub cap small (some 0) before.segment.memory p.step.Choice)
    (after : ∀ i, QuietInterval script pub cap small (some 0) (select.cut.part i).memory)
    (charge : ∀ i, RAMBuckets.cost Report.probes before.source.logs +
      RAMBuckets.cost Report.probes (select.source i).logs +
      RAMBuckets.cost Report.probes (after i).source.logs ≤ rate)
    (boundary : ∀ i, Boundary resident pub pitch total (loc.finish B) (past++[level o encode i])
      (p.next i) (after i).segment.memory) :
    PassRun resident pub pitch total cap small rate loc o encode past m := by
  let choose := select.atState before.state
  let endAt (i : p.step.Choice) := (after i).atState (choose.state i)
  let rest := choose.cut.afterChoice (fun i => (endAt i).segment)
    (fun i => (endAt i).segment.bits.length) (fun i => (endAt i).quiet)
  let combined := Cut.before before.segment before.segment.bits.length before.quiet rest
  let core (i : p.step.Choice) : OnlineWorkspace.Core script pub (combined.part i) small :=
    before.source.append ((choose.source i).append (endAt i).source)
  refine ⟨combined,?_,?_,core,?_,?_⟩
  · exact Cut.PrefixFrame.before before.segment before.segment.bits.length before.quiet before.stable
      (choose.frame.afterChoice (fun i => (endAt i).segment) (fun i => (endAt i).segment.bits.length)
        (fun i => (endAt i).quiet) (fun i => (endAt i).stable))
  · intro i
    change (before.segment.append ((choose.cut.part i).append (endAt i).segment)).state = some 0
    exact (Segment.append_state _ _).trans ((Segment.append_state (choose.cut.part i) (endAt i).segment).trans (endAt i).state)
  · intro i
    change RAMBuckets.cost Report.probes (before.source.logs ++ ((select.source i).logs ++ (after i).source.logs)) ≤ rate
    rw [RAMBuckets.cost_append,RAMBuckets.cost_append,← Nat.add_assoc]
    exact charge i
  · intro i
    change Boundary _ _ _ _ _ _ _ (before.segment.append ((choose.cut.part i).append (endAt i).segment)).memory
    have h := (Segment.append_memory before.segment ((choose.cut.part i).append (endAt i).segment)).trans
      (Segment.append_memory (choose.cut.part i) (endAt i).segment)
    exact h.symm ▸ boundary i

end CompressorRecords.ScheduledTrace

end

end VPVNP
end Computability
end OAI
