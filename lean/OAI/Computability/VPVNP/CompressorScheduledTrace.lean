import OAI.Computability.VPVNP.CompressorScheduledTraceData

/-! # Native execution in chronological block order -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.ScheduledTrace
open BurstRAM Compression BranchSegments PassTimeline PairSimulation.LocalHistory
open scoped Fin.CommRing
attribute [local irreducible] BlockProgram.script
open private collectLevels from OAI.Computability.VPVNP.CompressorExecutionLevels

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}
variable {w cap small rate total : ℕ} {pub : Fin 11 → Word w} {pitch : Word w}

local notation "script" => BlockProgram.script B
local notation "pt" => Workspace.ports (Schedule.arity (BlockPlanner.Script.catalog (BlockProgram.script B))) (pub 2)
local notation "outer" => OnlineWorkspace.program (BlockPlanner.Script.plan (BlockProgram.script B)) pub
local notation "lo" => Fin.val (pub 2)+6

variable {resident : Resident B f hf w} {a g b n : ℕ} {X : State a g}

theorem iterate
    (bounds : Schedule.Online.Run.ControlBounds (BlockPlanner.Script.plan script) cap (w := w))
    (smallBounds : Schedule.Online.Run.ControlBounds (BlockPlanner.Script.plan script) small (w := w))
    (E : StateExecution R b n X) (o : PassOrigins B f hf E) (W : E.MapWitnesses f) (r : ExecutionReaders E W)
    (past : List (SelectedLevel B f hf)) (ord : ℕ) (st : Option (Word w)) (m : Memory w) (hs : st = some 0)
    (xs : List (Located S.steps)) (order : ExecutionCalendar.Follows E o (xs.map Located.phase))
    (calendar : Consecutive B ord xs total) (pass : RunTree resident pub pitch total cap small rate E o W r xs past)
    (ready : Boundary resident pub pitch total ord past X m) :
    Nonempty (Result resident pub pitch total cap small (xs.length*rate+4) E o W r past st m) := by
  induction E generalizing past ord xs st m with
  | done X =>
    cases xs with
    | cons x xs => contradiction
    | nil =>
      subst st
      change ord = total at calendar
      subst ord
      have stop : m (pt).rows.val ≤ m (pt).ordinal.val := Fin.le_def.mpr (ready.totalValue.trans ready.ordinalValue.symm).le
      let seg := OnlineWorkspace.terminalSegment script pub bounds ready.tag ready.bank stop
      have halt : seg.state = none := OnlineWorkspace.terminalSegment_state ..
      let t : ExecutionTrace outer (cap+24) (.done X : StateExecution R _ _ X) (some 0) m := .done seg 1 rfl halt
      let core := OnlineWorkspace.terminalCore (A := script) (pub := pub) bounds smallBounds ready.tag ready.bank stop
      refine ⟨⟨t,?_,fun _ => core,fun _ => ?_,fun _ => ?_⟩⟩
      · exact OnlineWorkspace.terminalSegment_stable script pub bounds ready.tag ready.bank stop lo
      · simpa only [core,List.length_nil,Nat.zero_mul,Nat.zero_add] using
          (OnlineWorkspace.terminal_cost bounds smallBounds ready.tag ready.bank stop).le
      · change Boundary resident pub pitch total total (past++[]) X seg.memory
        rw [List.append_nil,OnlineWorkspace.terminalSegment_memory]; exact ready
  | more p tail ih =>
    cases xs with
    | nil => exact order.elim
    | cons loc rest =>
      subst st
      obtain ⟨hphase,phases⟩ := order
      obtain ⟨first,remaining⟩ := calendar
      let encode := r.1.select.encode
      let here := (pass.1 hphase m (first ▸ ready)).some
      let child (i : p.step.Choice) :=
        (ih i (o := o.2 i) (W := W.2 i) (r := r.2 i) (past := past++[level o.1 encode i])
          (ord := loc.finish B) (st := (here.cut.part i).state) (m := (here.cut.part i).memory)
          (hs := here.state i) (xs := rest) (order := phases i) (calendar := remaining) (pass := pass.2 i) (ready := here.next i)).some
      let t : ExecutionTrace outer (cap+24) (.more p tail) (some 0) m := .more here.cut fun i => (child i).trace
      refine ⟨⟨t,⟨here.frame,fun i => (child i).frame⟩,
        fun z => (here.source z.1).append ((child z.1).source z.2),?_,?_⟩⟩
      · intro z
        obtain ⟨i,u⟩ := z
        rw [OnlineWorkspace.Core.cost_append]
        have step := here.cost i
        have later := (child i).cost u
        simp only [List.length_cons,Nat.succ_mul]
        omega
      · intro z
        obtain ⟨i,u⟩ := z
        change Boundary resident pub pitch total total (past++level o.1 encode i :: collectLevels B f hf (tail i) _ _ _ u)
          _ (((here.cut.part i).append ((child i).trace.cut.part u)).memory)
        rw [Segment.append_memory]
        simpa only [List.append_assoc,List.singleton_append,StateExecution.finalState] using (child i).final u

end CompressorRecords.ScheduledTrace

end

end VPVNP
end Computability
end OAI
