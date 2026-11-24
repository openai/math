import OAI.Computability.VPVNP.CompressorBlockProgram
import OAI.Computability.VPVNP.CompressorSelectorGroupPost
import OAI.Computability.VPVNP.PairSimulationSelectorStart
import OAI.Computability.VPVNP.PairSimulationWorkspaceSelectorInterval

/-! # The selected term packet at its physical workspace boundary

The script's selector occurrence determines the native worker input and
the private clock. Its workspace interval consumes the term's worker tapes.
A source packet with those tapes therefore describes the memory and cost
of that particular branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScheduledTrace

open BurstRAM Compression DescriptorSpace Schedule SourceTransport PairSimulation.LocalHistory
open scoped Fin.CommRing
attribute [local irreducible] BlockProgram.script

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
    {A : Type*} [CommRing A] {f : B.Entry → A} {hf : B.IsSolution f}
    {a g b n w : ℕ} {X : State a g} {p : StatePass A X b n}

/-- Inputs and clock bounds at the actual calendar occurrence of the native term selector. -/
structure SelectorSite (o : PassOrigin B f hf p) (L : Layout) (pub : Fin 11 → Word w)
    (cap small : ℕ) (m : Memory w) (script : BlockPlanner.Script := BlockProgram.script B) where
  /-- Native worker input for the term selector at this occurrence in the scheduled block. -/
  I : WorkerInput o w
  /-- Index of this term-selector occurrence in the block planner's script. -/
  j : Fin script.size
  /-- Certificate that the selected calendar occurrence starts this worker on its intended row,
  with the recorded table, fuel, bounds, and input memory. -/
  start : I.SelectorBoundary script (pub 2) m cap j
  placement : ∀ i, levelStart L 0 ≤ (I.layout.base i).val
  recipeClock : (script.plan.recipes start.entry.phase).2.code.length + 1 + 2 * Online.N script.size script.size + 5 ≤ small
  dataClock : start.entry.fuel + 3 + 4 * ((script.catalog start.entry.worker).params + 1) + 2 * Online.N script.size script.size + 5 ≤ small

namespace SelectorSite

variable {o : PassOrigin B f hf p} {L : Layout} {pub : Fin 11 → Word w} {cap small : ℕ} {m : Memory w}

variable {script : BlockPlanner.Script}

variable (site : SelectorSite o L pub cap small m script)
    (bounds : Online.Run.ControlBounds script.plan cap (w := w))
    (smallBounds : Online.Run.ControlBounds script.plan small (w := w))
    (hg : arity script.catalog = L.shape.arity) (hb : (pub 2).val = L.base)
    (fit : levelStart L 0 < 2 ^ w) (bank : Workspace.Installed (arity script.catalog) (pub 2) m)
    (tag : m (Workspace.ports (arity script.catalog) (pub 2)).tag.val = LiveStageLink.tagWord w (Online.calendarIndex script.size script.size)) (live : m (Workspace.ports (arity script.catalog) (pub 2)).ordinal.val < m (Workspace.ports (arity script.catalog) (pub 2)).rows.val)
    (room : (m (Workspace.ports (arity script.catalog) (pub 2)).ordinal.val).val < directoryRows L)

/-- Execute the installed selector from calendar state zero at its two clocks. -/
noncomputable def interval : SelectorInterval script pub cap small (some 0) m p.step.Choice :=
  site.I.workspaceSelectorInterval script L pub site.start.entry bounds 0 tag live
    site.start.table site.start.fuel site.start.start site.start.stop site.start.memory
    hg hb fit bank room site.placement smallBounds site.recipeClock site.dataClock

local notation "out" => site.interval bounds smallBounds hg hb fit bank tag live room

/-- A physical branch consumes the entering control tapes, one worker tape per motif,
and the empty return tape. -/
theorem interval_bits (i : p.step.Choice) :
    ((out).cut.part i).bits = [] :: [] :: [] :: (List.ofFn (workerTapes o w i) ++ [[]]) := rfl

/-- Identify the memory and private-clock work of this physical branch with its source packet. -/
theorem interval_post (i : p.step.Choice) (pkt : SourceOnline.Packet script w)
    {raw : Memory w} {ordinal total : ℕ}
    (group : SourceOnline.Group script L (pub 2) small ordinal total raw [pkt])
    (tapes : pkt.stage.choices = List.ofFn (workerTapes o w i)) (totalRoom : total ≤ directoryRows L)
    (agree : Agree (levelStart L 0 ≤ ·) raw m)
    (ord : (m (Workspace.ports (arity script.catalog) (pub 2)).ordinal.val).val = ordinal) (rows : (m (Workspace.ports (arity script.catalog) (pub 2)).rows.val).val = total)
    (stride : m ((Workspace.ports (arity script.catalog) (pub 2)).directory - 1).val = (levelWords L : Word w)) :
    let mem := ((out).cut.part i).memory
    Agree (levelStart L 0 ≤ ·) pkt.output mem ∧ Workspace.Installed (arity script.catalog) (pub 2) mem ∧
      mem (Workspace.ports (arity script.catalog) (pub 2)).tag.val = LiveStageLink.tagWord w (Online.calendarIndex script.size script.size) ∧ (mem (Workspace.ports (arity script.catalog) (pub 2)).ordinal.val).val = ordinal + 1 ∧
      (mem (Workspace.ports (arity script.catalog) (pub 2)).rows.val).val = total ∧ mem ((Workspace.ports (arity script.catalog) (pub 2)).directory - 1).val = (levelWords L : Word w) ∧
      RAMBuckets.cost Report.probes ((out).source i).logs ≤ groupCost script [pkt] := by
  apply selectorGroupPost out i pkt group _ smallBounds hg hb fit _ totalRoom agree bank tag ord rows stride
  · rw [tapes]
    exact site.interval_bits bounds smallBounds hg hb fit bank tag live room i
  · exact ord ▸ rows ▸ Fin.lt_def.mp live

end SelectorSite
end CompressorRecords.ScheduledTrace

end VPVNP
end Computability
end OAI
