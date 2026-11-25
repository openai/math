import OAI.Hierarchy.GridPhysicalCompiler
import OAI.Hierarchy.TraceReceiverRuns
import OAI.Hierarchy.TraceNativeAdmittedWork

namespace OAI
/-! # Installing a single receiver for the physical compiler's chosen width -/
noncomputable section
namespace Hierarchy.GridPhysicalCompiler
open ThreeFlat Diagonal PhysicalStage RAM Computability.VPVNP.BurstRAM PrivateRAM
open GridScale GridInstalledEvaluator GridRegisteredSetting TraceDistribution PhysicalProcedure
open TickWeightedBank BitLayout Contraction TraceFactorReceiver

/-- In the physical S9/S10/S18 layout, both metadata and table fits follow
from the common clock and the public width, independently of the selected
root list. The padding header occupies four words at S18+48. -/
theorem workspace (F : Type) [Field F] [Fintype F] {W v p fuel : ℕ}
    (sized : 64≤TickWorkspace.stride v) (pins : p≤TickWorkspace.stride v)
    (clock : fuel≤TickWorkspace.stride v)
    (field : Fintype.card F*Fintype.card F≤TickWorkspace.stride v)
    (tables : 8*(TickTerminalPadding.tables F+2)≤TickWorkspace.stride v)
    (top : 21*TickWorkspace.stride v<2^W) :
    let H:=fuel/40000
    let C:=2*H
    let metaBase:=TickWorkspace.base v 9
    let lut:=TickWorkspace.base v 10
    let control:=TickWorkspace.base v 18
    let header:=control+48
    Fits (shape F p H C) W ∧ footprint (shape F p H C)≤ metaBase ∧
      footprint (shape F p H C)≤lut ∧ cellsBase p H≤ metaBase ∧ metaBase+4*C≤lut ∧
      lut+8*(TickTerminalPadding.tables F+2)≤header ∧ header+4<2^W ∧
      control+3<2^W ∧ control+4≤header ∧ 2+p+p<2^W := by
  intro H C metaBase lut control header
  let stride:=TickWorkspace.stride v
  have count : H*40000≤ stride := (Nat.div_mul_le_self fuel 40000).trans clock
  have footprintEq : footprint (shape F p H C)=2+p+H+11*C+Fintype.card F*Fintype.card F := rfl
  have cap : 2+p+H+11*C+Fintype.card F*Fintype.card F≤10*stride := by
    dsimp only [stride,C] at *
    omega
  change (2+p+H+11*C+Fintype.card F*Fintype.card F≤2^W) ∧ _
  rw [footprintEq]
  change _ ∧ _≤10*stride ∧ _≤11*stride ∧ 2+p+H≤10*stride ∧
    10*stride+4*C≤11*stride ∧ 11*stride+8*(TickTerminalPadding.tables F+2)≤19*stride+48 ∧
    19*stride+48+4<2^W ∧ 19*stride+3<2^W ∧ 19*stride+4≤19*stride+48 ∧ 2+p+p<2^W
  dsimp only [stride,C] at *
  omega


variable {F : Type} [Field F] [Fintype F] {blk : Block F}
    {m A w degree stageRate rootRate J r : ℕ} {Q : ℕ→ℕ} {loss : ℕ→ℝ}
    {v : TickSelection F (m+1) A w Q loss}
    (I : Installed blk m A w degree stageRate rootRate v)
    (R : GridInstalledFit.Receipt blk m A w degree stageRate rootRate v I J r)
local notation "l" => GridInstalledEvaluator.layout m A w (overhead Q loss w) v.copies degree stageRate rootRate
local notation "D" => I.D
local notation "W" => 64*w
set_option quotPrecheck false in
local notation "N" => (l).pinWidth
local notation "arch" => GridDescription.capacity w

/-- The same repeated physical plan, including the true recast of its number
of lanes, supplies the assembly used by the selected-node evaluator. -/
def receiverAssembly : (D).run.Assembler (Fin I.inputSize→Bool) := by
  let P:=(D).block.repeat (D).passes
  let rem:=I.axes+1-P.charge
  have split : I.axes+1=P.charge+rem := by
    dsimp only [P,rem];rw [(D).block.charge_repeat];have := (D).passesFit;omega
  exact (Physical.registerOnLanes (D).block (Fin I.inputSize→Bool) (D).passes rem _ split).1


set_option maxHeartbeats 1600000 in
/-- Install one padded program independently of the selector. Its native archive
and source producer must satisfy the selected-children contract on each successful
parse of the true packet table. On those runs the weighted field interpreter
computes the physical root factors required by the installed evaluator. -/
theorem receiverAt_of_streams {H C : ℕ} (fit : Fits (shape F N H C) W) (src : Procedure W)
    (cursor control cmdBase header «meta» lut : ℕ) (large : 1024≤w)
    (hp : (dimensions (TraceReceiverProgram.machine fit src cursor control header «meta» lut)).1≤arch)
    (hr : (dimensions (TraceReceiverProgram.machine fit src cursor control header «meta» lut)).2.1≤arch)
    (hk : (dimensions (TraceReceiverProgram.machine fit src cursor control header «meta» lut)).2.2≤arch)
    (wide : 4<2^W) (metaSpace : footprint (shape F N H C)≤«meta»)
    (lutSpace : footprint (shape F N H C)≤lut) (frame : cellsBase N H≤«meta»)
    (rows : «meta»+4*C≤lut) (tables : lut+8*(TickTerminalPadding.tables F+2)≤header)
    (headRoom : header+4<2^W) (ctrlRoom : control+3<2^W)
    (apart : control+4≤header ∨ header+4≤control) (shiftRoom : 2+N+N<2^W)
    (compiled :
      let recv:=CapacityPadding.pad (TraceReceiverProgram.machine fit src cursor control header «meta» lut) hp hr hk
      let gateBase:=26*GridDescription.sector w
      let rooms:=(R.rooms recv 0 gateBase).choose
      let widths:=fun i=>(v.replacement.width_le_size i).trans v.size_le
      ∀ safe : GridNativeDispatch.WordRoom D,
        ReceiverStreams I recv 0 gateBase R.text rooms widths (GridNativeDispatch.actualTable D safe).codes
          (GridNativeDispatch.selectorRoom D l R.table R.selector safe) (H:=H) (J:=C)
          src cursor control cmdBase «meta» (receiverAssembly I)) :
    ReceiverAt blk m degree stageRate rootRate J r v I R := by
  let recv:=CapacityPadding.pad (TraceReceiverProgram.machine fit src cursor control header «meta» lut) hp hr hk
  refine ⟨recv,?_⟩
  intro rooms widths safe
  exact runs_of_streams I recv 0 (26*GridDescription.sector w) R.text rooms widths _ _
    fit src cursor control cmdBase header «meta» lut hp hr hk rfl large wide metaSpace lutSpace
    frame rows tables headRoom ctrlRoom apart shiftRoom (receiverAssembly I) (compiled safe)

end Hierarchy.GridPhysicalCompiler
end

end OAI
