import OAI.Hierarchy.GridChosenReceiverExecution
import OAI.Hierarchy.GridChosenReceiverWires
import OAI.Hierarchy.TraceReceiverRootFrame
import OAI.Hierarchy.GridChosenReceiverFlat

namespace OAI
/-! # Passing actual compiled descendant rows and terminal maps to the grid diagonal -/

noncomputable section
namespace Hierarchy.GridChosenReceiver
open ThreeFlat Diagonal Diagonal.HistoryContraction Diagonal.PhysicalStage
open RAM RAM.PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM TraceDistribution GridScale GridThrough
open GridRegisteredSetting GridInstalledEvaluator Filter
open TraceFactorReceiver TraceFactorReceiver.Gather
open scoped BigOperators Classical

variable {F : Type} [Field F] [Fintype F] {B : Block F} {m A w : ℕ}
variable {Q : ℕ→ℕ} {loss : ℕ→ℝ} {v : TickSelection F (m+1) A w Q loss}
variable (I : Installed B m A w (degree B) (stageRate B) rootRate v)
variable (R : GridInstalledFit.Receipt B m A w (degree B) (stageRate B) rootRate v I reserve 0)
set_option quotPrecheck false
local notation "D" => I.D
local notation "l" => layout m A w (overhead Q loss w) v.copies (degree B) (stageRate B) rootRate
local notation "n" => (l).sideMinusOne
local notation "channels" => GridControllerSimGeometry.railCount m n (l).bank
local notation "W" => (64*w)
local notation "gate" => (26*GridDescription.sector w)
local notation "arch" => GridDescription.capacity w
local notation "p" => (l).pinWidth
local notation "clock" => UniversalTick.clock w UniversalTick.saving
local notation "H" => (clock/40000)
local notation "V" => TraceAdmission.receiverAge w
local notation "units" => (D).issuedUnit w (degree B) (stageRate B) rootRate
local notation "widths" => (fun i=>(v.replacement.width_le_size i).trans v.size_le)
local notation "U" => TraceReceiverSeedWords.wordsLayout (D).machine (D).fit (D).field (D).state (D).block (D).axesFit
local notation "trees" => TraceReceiverSeedWords.forest (D).machine (D).fit (D).field (D).state (D).block (D).axesFit
local notation "work" => (fun (z : I.D.trace) => (D).work z.1 (D).issuedCharges units)
local notation "cost" => (fun (z : I.D.trace) => (D).costs (GridNativeImage.resources D l) z.1 m n (l).bank (D).issuedCharges units)
local notation "group" => (fun (z : I.D.trace) (c : Cell (m+1) n) (j : Fin v.copies) => FactorAllocation.factors w (cost z) (List.ofFn id) (GridTicks.index (c,j)))
local notation "chosen" => (fun (z : I.D.trace) => (D).run.plan.assemble z.1 ((GridPhysicalCompiler.receiverAssembly I) U) trees)
local notation "which" => (fun (z : I.D.trace) => ((D).ordinal z.1).symm)
local notation "fixed" => (fun (z : I.D.trace) => (D).run.terminalLabels z.1 z.2)
local notation "table" => (fun (safe : GridNativeDispatch.WordRoom I.D) => (GridNativeDispatch.actualTable D safe).codes)
local notation "room" => (fun (safe : GridNativeDispatch.WordRoom I.D) => GridNativeDispatch.selectorRoom D l R.table R.selector safe)
local notation "rooms" => (fun (recv : Machine W arch arch arch) => (R.rooms recv 0 gate).choose)
local notation "input" => (fun (recv : Machine W arch arch arch) (safe : GridNativeDispatch.WordRoom I.D) (z : I.D.trace) => streamInput I recv 0 gate R.text (rooms recv) widths
  (table safe) (room safe) z)
local notation "salt" => (fun (recv : Machine W arch arch arch) (x : GridDiagonal.Pins (Fin channels)) => (fun i : Fin I.inputSize=>GridDescription.input (x ∘ UniversalGrid.Wiring.railPin.symm)
  (GridDescription.code (q:=w^2) recv (D).machine) (GridNativeDispatch.source D l v.replacement 0 gate) i.val))

/-- The two remaining slices have their own original RAM program and coherent
memory. The payload equation reads a particular issued root at the real pin
used by its persisted map. The fee includes gathering that map into the field
evaluator, whose fixed cost is provided by the chosen scale. -/
def LocalPhases (geom : GridReceiverDirectory.ElectionRoom D l) : Prop :=
  ∀ (recv : Machine W arch arch arch) (safe : GridNativeDispatch.WordRoom D)
    (z : (D).trace) (x : GridDiagonal.Pins (Fin channels)) (c : Cell (m+1) n) (j : Fin v.copies),
    let sites : List (Fin ((D).roots z.1)) := group z c j
    let outs:=chosen z
    let who:=which z
    let tape:=input recv safe z x c j
    let pinMem:=GridReceiverDirectory.shifted l w tape
    let sel:=GridReceiverDirectory.InputWindow D l z safe (room safe)
    let origin:=GridReceiverDirectory.original D l sel tape
    let eligible:=GridReceiverDirectory.Elected D l geom safe z sel (GridTicks.index (c,j)) pinMem origin
    let wire:=slotWire I R geom recv safe z c j
    let spans:=List.ofFn (Gather.rootSpan (TickWorkspace.base V 9)
      (fun i : Fin sites.length=>(outs.2 (who (sites.get i))).compile.cells))
    ∃ (replay finish : ℕ) (cache : Memory W → Memory W → Prop),
      28+16*p+((GridReceiverDirectory.prefixTime D l+(replay+finish))+Gather.fuel spans)≤
        setupTime D l+65536*(∑ i : Fin sites.length, (work z) (sites.get i)) ∧
      (∀ m,eligible m → (descendants D l).Spec (·=m) (fun _=>cache m) replay) ∧
      (∀ m q,eligible m → cache m q → (terminal D l).Spec (·=q) (fun _ out=>
        Gather.Prepared (fun i : Fin sites.length=>(outs.2 (who (sites.get i))).compile)
          (ctrl:=GridReceiverBanks.cursor w) (control:=TickWorkspace.base V 18)
          (atCmd:=GridReceiverBanks.commands w) («H»:=H) wire (fun i:Fin p=>tape i.val)
          (TickWorkspace.base V 9) spans out) finish)

set_option maxHeartbeats 1200000 in
theorem compiled_of_local (geom : GridReceiverDirectory.ElectionRoom D l)
    (prefixRun : InstalledPrefix I R geom) (localRuns : LocalPhases I R geom)
    (rows : ∀ h i,10000*(((D).issuedTree h i).compile.cells+((D).issuedTree h i).compile.internal)≤
      (D).work h (D).issuedCharges units i)
    (setup : 4*setupTime D l≤clock) (field : 4*fieldCost F≤clock) :
    Compiled I R := by
  intro fit capacity recv gateAddr rr width safe z x c j
  dsimp only
  let sites : List (Fin ((D).roots z.1)) :=
    FactorAllocation.factors w (cost z) (List.ofFn id) (GridTicks.index (c,j))
  let net := fun i : Fin sites.length=>(D).issuedTree z.1 (sites.get i)
  let fee := fun i : Fin sites.length=>(work z) (sites.get i)
  let wire:=slotWire I R geom recv safe z c j
  let spans:=List.ofFn (Gather.rootSpan (TickWorkspace.base V 9) (fun i : Fin sites.length=>(net i).compile.cells))
  have correct:=slotWire_read I R geom recv safe z x c j
  obtain ⟨replay,finish,saved,bill,descend,maps⟩:=localRuns recv safe z x c j
  have dimensions (i : Fin sites.length) : 10000*((net i).compile.cells+(net i).compile.internal)≤fee i :=
    rows z.1 (sites.get i)
  have paid:=paid_phases D l net wire (fun i:Fin p=>input recv safe z x c j i.val) spans clock
    (setupTime D l) (GridReceiverDirectory.prefixTime D l) replay finish fee dimensions
    (slot_bill I R recv z (c,j)) setup field bill _ saved (prefixRun recv safe z x c j) descend maps
  exact ⟨wire,spans,_,correct,paid⟩

/-- All common and per-slot estimates are consequences of the same installed
receipt. Only the two physical operations on issued streams remain here. -/
theorem receives_of_local (B : Block F) (m cutoff : ℕ)
    (run : ∀ A>max cutoff (UniversalTick.saving+2+(0+51)),∀ Q loss,
      Envelopes Q loss → ∀ q : ℕ→ℕ,(∀ᶠ w : ℕ in atTop,0<q w ∧ q w≤Q w) →
        ∀ᶠ w : ℕ in atTop,∀ t : ℕ,5120≤t → 64*w=16*t^10 → Even w →
          ∀ (v : TickSelection F (m+1) A w Q loss),v.copies=q w →
          ∀ (I : Installed B m A w (degree B) (stageRate B) rootRate v)
            (R : GridInstalledFit.Receipt B m A w (degree B) (stageRate B) rootRate v I reserve 0)
            (geom : GridReceiverDirectory.ElectionRoom I.D
              (layout m A w (overhead Q loss w) v.copies (degree B) (stageRate B) rootRate)),
            LocalPhases I R geom) : Receives B m := by
  refine ⟨cutoff,?_⟩
  intro A large Q loss env q valid
  filter_upwards [eventual_installed_prefix B env m A (degree B) (stageRate B) rootRate q valid,
    eventual_slot_rows B m A env q valid,field_clock B m A env q valid,
    run A large Q loss env q valid] with w navigation sites clocks localRuns
  intro t cutoffAge eqn even v copies I R
  obtain ⟨geom,entry⟩:=navigation v copies I R
  have space:=clocks v copies I
  exact compiled_of_local I R geom entry (localRuns t cutoffAge eqn even v copies I R geom)
    (sites v copies I) space.1 space.2


end Hierarchy.GridChosenReceiver
end

end OAI
