import OAI.Computability.VPVNP.CompressorPassIntervalData
import OAI.Computability.VPVNP.PairSimulationWorkspacePrefix

/-! # The physical selector interval and its row-specific source clock -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open Compression CompressorRecords CompressorRecords.SelectedTerms NetworkKernel BurstRAM
open CompressorRecords.Schedule CompressorRecords.Schedule.Online
open DescriptorSpace BlockPlanner SourceTransport
open scoped Fin.CommRing

variable {k : Type*} [Field k] {S : BlockSchedule k} {B : S.Templates}
  {A : Type*} [CommRing A] {f : B.Entry → A} {hf : B.IsSolution f}
  {a g b n w cap : ℕ} {X : State a g} {p : StatePass A X b n} {o : PassOrigin B f hf p}

variable (I : WorkerInput o w) (script : Script) (L : DescriptorSpace.Layout) (pub : Fin 11 → Word w)
local notation "pt" => Workspace.ports (arity script.catalog) (pub 2)
local notation "H" => levelStart L 0

open BranchSegments

variable {m : Memory w} (entry : Run.RowStart script.plan (OnlineWorkspace.ports (C := script.catalog) pub) cap m)
    (controls : Run.ControlBounds script.plan cap (w := w)) (state : Word w)
    (tag : m (OnlineWorkspace.ports (C := script.catalog) pub).tag.val = LiveStageLink.tagWord w (calendarIndex script.size script.size))
    (live : m (OnlineWorkspace.ports (C := script.catalog) pub).ordinal.val < m (OnlineWorkspace.ports (C := script.catalog) pub).rows.val) (installed : RowStartTable entry = I.table)
    (fuel : entry.fuel = I.fuel) (start : Directory.start script.catalog (OnlineWorkspace.ports (C := script.catalog) pub) (rowInput script.plan (OnlineWorkspace.ports (C := script.catalog) pub) m entry.phase) = 0)
    (stop : (Directory.bound script.catalog (OnlineWorkspace.ports (C := script.catalog) pub) (rowInput script.plan (OnlineWorkspace.ports (C := script.catalog) pub) m entry.phase)).val = o.motifCount)
    (memory : Directory.prepared script.catalog (OnlineWorkspace.ports (C := script.catalog) pub) (rowInput script.plan (OnlineWorkspace.ports (C := script.catalog) pub) m entry.phase) = I.memory)
    (hg : arity script.catalog = L.shape.arity) (hb : (pub 2).val = L.base) (fit : levelStart L 0 < 2^w)
    (bank : Workspace.Installed (arity script.catalog) (pub 2) m)
    (room : (m (OnlineWorkspace.ports (C := script.catalog) pub).ordinal.val).val < directoryRows L) (placement : ∀ i, levelStart L 0 ≤ (I.layout.base i).val)
local notation "framedCut" => I.workspaceSelectorCut script L pub entry controls state tag live installed fuel
  start stop memory hg hb fit bank room placement
local notation "selected" => I.selectedStep entry


variable {small : ℕ} (smallBounds : Run.ControlBounds script.plan small (w := w))
    (recipeClock : (script.plan.recipes entry.phase).2.code.length+1+2*N script.size script.size+5 ≤ small)
    (dataClock : entry.fuel+3+4*((script.catalog entry.worker).params+1)+2*N script.size script.size+5 ≤ small)

/-- The physical selector at the outer clock, with the exact same inner row
reports verified at the smaller computational clock used for charging. -/
noncomputable def WorkerInput.workspaceSelectorInterval :
    ScheduledTrace.SelectorInterval script pub cap small (some state) m p.step.Choice where
  cut := framedCut
  frame := I.workspaceSelectorCut_prefixFrame script L pub entry controls state tag live installed fuel start stop memory
    hg hb fit bank room placement
  state := I.workspaceSelectorCut_state script L pub entry controls state tag live installed fuel start stop memory
    hg hb fit bank room placement
  source i :=
    let s := (selected) i
    let valid := I.selectedStep_valid entry live installed fuel start stop memory i
    let short : s.Valid script.plan pt small m := ⟨valid.phase,valid.active,valid.input,valid.source,recipeClock,dataClock⟩
    ⟨rowLog script.plan pt m s.phase s.row, (Run.oneRow script.plan pt (state := state) smallBounds tag s short).run,rfl⟩

local notation "interval" => I.workspaceSelectorInterval script L pub entry controls state tag live installed fuel
  start stop memory hg hb fit bank room placement smallBounds recipeClock dataClock

/-- Exact cost of this interval in terms of its native term-worker reports,
the active arity and the recipe metadata reads. -/
theorem WorkerInput.workspaceSelectorInterval_cost (i : p.step.Choice) :
    let raw := (I.selected_run i).choose
    RAMBuckets.cost Report.probes ((interval).source i).logs =
      RAMBuckets.cost Report.probes raw + raw.length*((script.catalog entry.worker).params+2) +
        (script.plan.recipes entry.phase).2.reads + 3*arity script.catalog + (script.catalog entry.worker).params + 26 :=
  row_cost script.plan pt m entry.phase ((selected) i).row
    (I.selectedStep_valid entry live installed fuel start stop memory i).source

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
