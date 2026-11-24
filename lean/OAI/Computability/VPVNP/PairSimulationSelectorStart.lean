import OAI.Computability.VPVNP.CompressorTermRowStart
import OAI.Computability.VPVNP.CompressorSelectedTermWorker
import OAI.Computability.VPVNP.PairSimulationWorkerCut

/-! # Entering the selected motif table in the actual block script

The directory's start, exclusive bound, and instantiated worker table
are read back from the current physical recipe. The same boundary
supplies the native selector cut at the current RAM and clock.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open Compression CompressorRecords CompressorRecords.SelectedTerms NetworkKernel BurstRAM
open CompressorRecords.Schedule CompressorRecords.Schedule.Online DescriptorSpace BlockPlanner
open scoped Fin.CommRing

variable {k : Type*} [Field k] {S : BlockSchedule k} {B : S.Templates}
  {A : Type*} [CommRing A] {f : B.Entry → A} {hf : B.IsSolution f}
  {a g b n w : ℕ} {X : State a g} {p : StatePass A X b n} {o : PassOrigin B f hf p}

private abbrev scriptPorts (script : Script) (base : Word w) := Workspace.ports (arity script.catalog) base

/-- Interface of the physical calendar occurrence used by the branch cut. -/
structure WorkerInput.SelectorBoundary (I : WorkerInput o w) (script : Script) (base : Word w)
    (m : Memory w) (cap : ℕ) (j : Fin script.size) where
  /-- The row-start witness for the live selector occurrence at the current script memory and
  instruction cap. -/
  entry : Run.RowStart script.plan (Workspace.ports (arity script.catalog) base) cap m
  phase : entry.phase = j
  worker : entry.worker = j
  fuel : entry.fuel = I.fuel
  table : RowStartTable entry = I.table
  start : Directory.start script.catalog (Workspace.ports (arity script.catalog) base)
    (rowInput script.plan (Workspace.ports (arity script.catalog) base) m entry.phase) = 0
  stop : (Directory.bound script.catalog (Workspace.ports (arity script.catalog) base)
    (rowInput script.plan (Workspace.ports (arity script.catalog) base) m entry.phase)).val = o.motifCount
  memory : Directory.prepared script.catalog (Workspace.ports (arity script.catalog) base)
    (rowInput script.plan (Workspace.ports (arity script.catalog) base) m entry.phase) = I.memory

/-- Build the selector boundary at the current calendar row from its evaluated recipe operands,
memory, and clock bounds, identifying the installed worker and its motif interval. -/
noncomputable def WorkerInput.selectorStart (I : WorkerInput o w) (script : Script) (outer : DescriptorSpace.Layout)
    (base : Word w) (hg : arity script.catalog = outer.shape.arity) (hb : base.val = outer.base)
    (fit : levelStart outer 0 < 2^w) (m : Memory w) {cap : ℕ} (j : Fin script.size)
    (code : script.catalog j = TermWorker.motifPass (grid o).block (grid o).demandOrder.entries (grid o).e)
    (width : SelectedTermWorker.fitConstant B + 4*Nat.clog 2 (X.maxWireWidth+1) ≤ w)
    (readable : ∀ i, levelStart outer 0 ≤ (I.layout.source i).val)
    (writable : ∀ i, levelStart outer 0 ≤ (I.layout.base i).val)
    (start : script.operand base m j (script.visit j).initial = 0)
    (stop : (script.operand base m j (script.visit j).stop).val = o.motifCount)
    (args : ∀ i, script.operand base m j ((script.visit j).params i) =
      TermWorker.catalogWords (grid o).block (grid o).demandOrder.entries (grid o).supplyOrder.entries script.catalog j I.addr code i)
    (phase : (calendar script.plan).phase (m (scriptPorts script base).ordinal.val).val = j.val)
    (room : (m (scriptPorts script base).ordinal.val).val < directoryRows outer)
    (active : m (scriptPorts script base).ordinal.val < m (scriptPorts script base).rows.val)
    (recipeCap : (script.plan.recipes j).2.code.length+1+2*N script.size script.size+5 ≤ cap)
    (dataCap : I.fuel+3+4*((script.catalog j).params+1)+2*N script.size script.size+5 ≤ cap)
    (fresh : Directory.prepared script.catalog (scriptPorts script base) (rowInput script.plan (scriptPorts script base) m j) = I.memory) :
    I.SelectorBoundary script base m cap j := by
  let G := grid o
  let port := Workspace.ports (arity script.catalog) base
  have countFit : o.motifCount < 2^w := stop ▸ (script.operand base m j (script.visit j).stop).isLt
  have stopWord : script.operand base m j (script.visit j).stop = (o.motifCount : Word w) :=
    Fin.ext (stop.trans (Nat.mod_eq_of_lt countFit).symm)
  have agree := OnlineFootprint.prepared script outer base hg hb fit m j room
  rw [fresh] at agree
  have boundaryInputs : TermRecordScan.Inputs G.demandOrder.entries I.layout (termRows o).demand m := by
    intro i
    funext x
    obtain ⟨l,rfl⟩ := G.demandOrder.entries.surjective x
    rw [DemandPreparation.demandAt_address G.demandOrder.entries _ _ (I.layout.sourceFits i)]
    have hr := congrFun (I.inputs i) (G.demandOrder.entries l)
    rw [DemandPreparation.demandAt_address G.demandOrder.entries _ _ (I.layout.sourceFits i)] at hr
    exact (congrArg Fin.val (agree _ ((readable i).trans (Nat.le_add_right ..)))).trans hr
  let entry := TermWorker.rowStart G.block G.demandOrder.entries G.supplyOrder.entries G.pPos G.qPos
    script outer base hg hb fit m j code I.layout I.addr I.addresses (termRows o).demand (termRows o).bounded
    ((Nat.add_le_add_right (SelectedTermWorker.frameFit_le o) _).trans width) I.clock countFit readable writable
    boundaryInputs stopWord args phase room active recipeCap dataCap
  have snap := SourceOnline.evaluated_launch script base outer hg hb fit m j I.fuel [] room active
  refine ⟨entry,rfl,rfl,rfl,?_,snap.start.trans start,(congrArg Fin.val snap.stop).trans stop,fresh⟩
  let r : Directory.Row script.size w := ⟨rowInput script.plan port m j,j,I.fuel,[],[]⟩
  exact I.installed_of_words (ports := port) r code (fun i => (congrFun snap.params i).trans (args i))

/-- The typed boundary provides the cut at the actual stage memory. -/
noncomputable def WorkerInput.SelectorBoundary.cut {I : WorkerInput o w} {script : Script}
    {base : Word w} {m : Memory w} {cap : ℕ} {j : Fin script.size}
    (v : I.SelectorBoundary script base m cap j) (controls : Run.ControlBounds script.plan cap (w := w))
    (state : Word w) (tag : m (scriptPorts script base).tag.val = LiveStageLink.tagWord w (calendarIndex script.size script.size))
    (live : m (scriptPorts script base).ordinal.val < m (scriptPorts script base).rows.val) :
    BranchSegments.Cut (program script.plan (scriptPorts script base)) cap (some state) m p.step.Choice :=
  I.selectorCut v.entry controls state tag live v.table v.fuel v.start v.stop v.memory

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
