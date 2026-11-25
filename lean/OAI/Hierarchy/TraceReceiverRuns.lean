import OAI.Hierarchy.GridInstalledDistribution
import OAI.Hierarchy.TraceReceiverProgram
import OAI.Hierarchy.TraceReceiverSeedWords

namespace OAI
/-! # The installed grid's receiver value from its actual allocated streams -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.GridInstalledEvaluator
open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open RAM Computability.VPVNP.BurstRAM PrivateRAM UniversalGrid TraceDistribution GridThrough GridScale GridRegisteredSetting
open RAM.PhysicalProcedure TickWeightedBank BitLayout Contraction TraceFactorReceiver
open scoped Classical BigOperators
private def selectedStreams {F : Type} [Field F] [Fintype F] {W pinCount H J : ℕ} (src : Procedure W)
    (cursor control cmdBase «meta» fuel : ℕ) {S : HistoryContraction.Shape} {Pins α : Type*}
    (plan : Plan F S) (h : plan.History) {V : Form S Pins} (assembled : plan.Assembly V)
    (treeSeed : Forest F V) (bitsAt : Pins) (boundaryBits : (plan.finish h).Boundary)
    (groupIds : List α) (atSite : α → (plan.finish h).Site) (input : ℕ → Bool) : Prop :=
  let selected := plan.assemble h assembled treeSeed
  let nets := fun i : Fin groupIds.length => (selected.2 (atSite groupIds[i])).compile
  ∃ (wire : ∀ i : Fin groupIds.length, Fin (selected.1.width (atSite groupIds[i])) → Fin pinCount)
    (spans : List Gather.Span) (price : ℕ),
    let N := forest nets wire
    let pad := H-N.internal
    let fill := J-(N.cells+pad)
    (∀ i j, input (wire i j).val = selected.1.read (atSite groupIds[i]) bitsAt
      ((plan.finish h).graph.atVertex boundaryBits (atSite groupIds[i])) j) ∧
    N.internal ≤ H ∧ N.cells+pad ≤ J ∧
    src.Spec (·=TickMountedPins.memory (w:=W) (fun i : Fin pinCount => input i.val))
      (fun _ out => Gather.Prepared nets (ctrl:=cursor) (control:=control) (atCmd:=cmdBase) (H:=H)
        wire (fun i : Fin pinCount => input i.val) «meta» spans out) price ∧
    (28+16*pinCount+(price+Gather.fuel spans)+TickTerminalPadding.budget F pad fill)+evalCost F H J ≤ fuel

variable {F : Type} [Field F] [Fintype F] {Q : ℕ→ℕ} {loss : ℕ→ℝ}

variable {m A w degree stageRate rootRate : ℕ} {blk : Block F}
variable {v : TickSelection F (m+1) A w Q loss}
variable (I : Installed blk m A w degree stageRate rootRate v)
local notation "age" => overhead Q loss w
local notation "l" => layout m A w age v.copies degree stageRate rootRate
local notation "D" => I.D
local notation "X" => v.replacement
local notation "B" => pairs A w v.copies
local notation "n" => side age-1
local notation "arch" => GridDescription.capacity w
local notation "cap" => (l).selectorCap
local notation "railCount" => GridControllerSimGeometry.railCount m n B
local notation "dir" => GridIdleLayout.direction («m»:=m) («n»:=n) («B»:=B)
local notation "grades" => GridPhysicalSelector.bits (D).run
variable (recv : Machine (64*w) (GridDescription.capacity w)
  (GridDescription.capacity w) (GridDescription.capacity w)) (raw gateBase : ℕ)
variable (textFits : (layout m A w (overhead Q loss w) v.copies degree stageRate rootRate).receiverText ≤ w^2)
variable (rooms : GridNativeDispatch.Rooms I.D
  (layout m A w (overhead Q loss w) v.copies degree stageRate rootRate) recv raw gateBase textFits)
variable (widths : ∀ i, v.replacement.width i ≤ pairs A w v.copies)
variable (C : I.D.run.plan.Codes) (room : GridSelector.Room I.D.run.plan C
  (GridPhysicalSelector.bits I.D.run) (layout m A w (overhead Q loss w) v.copies degree stageRate rootRate).selectorCap)
local notation "chosen" => GridNativeDispatch.setting D l X recv raw gateBase textFits rooms widths v.active C room
local notation "suffix" => GridNativeDispatch.source D l X raw gateBase
local notation "code" => GridDescription.code (q:=w^2) recv (D).machine
local notation "tape" => (fun x : GridDiagonal.Pins (Fin railCount) =>
  GridDescription.input (x ∘ Wiring.railPin.symm) code suffix)
local notation "seed" => (fun x : GridDiagonal.Pins (Fin railCount) =>
  Physical.seed (D).block (D).axesFit (TraceDistribution.layout (D).machine (D).fit (D).field (D).state)
    (fun j => tape x j.val))
local notation "cost" => (fun z : (D).trace => (D).costs (GridNativeImage.resources D l) z.1 m n B
  (D).issuedCharges ((D).issuedUnit w degree stageRate rootRate))

local notation "rawPin" => (fun (x : GridDiagonal.Pins (Fin railCount)) (i : Fin I.inputSize)=>tape x i.val)
local notation "U" => TraceReceiverSeedWords.wordsLayout (D).machine (D).fit (D).field (D).state (D).block (D).axesFit
local notation "trees" => TraceReceiverSeedWords.forest (D).machine (D).fit (D).field (D).state (D).block (D).axesFit
local notation "machineClock" => UniversalTick.clock w UniversalTick.saving
local notation "localPins" => (l).pinWidth
local notation "items" => (fun (z : (D).trace) (c : Cell (m+1) n) (j : Fin v.copies) => FactorAllocation.factors w (cost z) (List.ofFn id) (GridTicks.index (c,j)))
local notation "root" => (fun (z : (D).trace) => (GridPhysicalSelector.siteOrder (D).run z.1).symm)
local notation "boundary" => (fun (z : (D).trace) => (D).run.terminalLabels z.1 z.2)

/-- The actual scheduled compact pins extended by zero after their visible range. -/
def streamInput (z : (D).trace) (x : GridDiagonal.Pins (Fin railCount)) (c : Cell (m+1) n)
    (j : Fin v.copies) (i : ℕ) : Bool :=
  if hi : i<localPins then (chosen (some z)).1.dataBits x c (finProdFinEquiv (j,⟨i,hi⟩)) else false

local notation "args" => GridNativeDispatch.params D l raw gateBase
local notation "flag" => (fun (z : (D).trace) => GridSelector.encode (D).run.plan C grades cap room (some z))
local notation "hdr" => (fun (z : (D).trace) (c : Cell (m+1) n) (j : Fin v.copies) => GridRegisteredPublication.headers (m:=m) («n»:=n) (q:=v.copies)
  D args recv (flag z) textFits (c,j))

/-- Every header bit occurs among the actual local pins chosen by the native
factor layout. Consequently the two-directory header initializes the same RAM
as the one used in the receiver's local product computation. -/
theorem stream_header (z : (D).trace) (x : GridDiagonal.Pins (Fin railCount)) (c : Cell (m+1) n)
    (j : Fin v.copies) :
    let head:=hdr z c j
    head.length≤localPins ∧ ∀ i : Fin head.length,
      streamInput I recv raw gateBase textFits rooms widths C room z x c j i.val=head[i.val] := by
  intro head
  have bounds:=rooms (flag z) z
  have len : head.length≤localPins := (bounds.headers (c,j)).trans ((Nat.le_add_right ..).trans bounds.pin_limit)
  refine ⟨len,?_⟩
  intro i
  let pin : Fin localPins:=⟨i.val,i.isLt.trans_le len⟩
  have entry : (chosen (some z)).1.data c (finProdFinEquiv (j,pin))=Sum.inr head[i.val] := by
    have paired {E : Type} {inputCount roots : ℕ} (rail : E ↪ Fin (inputCount/2))
        (origin : Fin inputCount → Fin roots)
        (whole : ∀ (k : ℕ) (hi : 2*k+1 < inputCount),
          origin ⟨2*k,by omega⟩=origin ⟨2*k+1,hi⟩) (e : E) :
        origin (FactorPinIntervals.pairPorts rail (e,true))=
          origin (FactorPinIntervals.pairPorts rail (e,false)) :=
      (whole (rail e).val (by have := (rail e).isLt; omega)).symm
    apply GridThrough.PinAssignment.ofFactorIntervals_header (t:=(c,j)) (i:=pin)
    · intro e
      exact paired _ ((D).origin z.1)
        (Physical.origin_pair (D).block (D).axesFit (D).machine (D).fit (D).field (D).state
          (D).passes (D).passesFit z.1 ((D).ordinal z.1)) e
  change (if H : i.val<localPins then _ else false)=_
  rw [dite_eq_left pin.isLt]
  change ((chosen (some z)).1.data c (finProdFinEquiv (j,pin))).elim _ id=_
  rw [entry]
  rfl

open scoped Fin.CommRing in
theorem stream_authentic (large : 1024≤w) (z : (D).trace) (x : GridDiagonal.Pins (Fin railCount))
    (c : Cell (m+1) n) (j : Fin v.copies)
    (i : Fin (SelfAdvice.textSize (64*w) arch arch)) :
    streamInput I recv raw gateBase textFits rooms widths C room z x c j i.val=NativeTrace.executable recv i := by
  have codeRoom:=GridDescription.room (w:=w) large
    (p:=arch) (k:=arch) (p':=arch) (k':=arch) le_rfl le_rfl le_rfl le_rfl
  have inside : i.val<(hdr z c j).length := by
    rw [GridReceiverHeader.length]
    change i.val<SelfAdvice.textSize (64*w) arch arch+_
    exact i.isLt.trans_le (Nat.le_add_right _ _)
  exact ((stream_header I recv raw gateBase textFits rooms widths C room z x c j).2 ⟨i.val,inside⟩).trans
    (GridReceiverHeader.authentic (w:=w) (text:=(l).receiverText)
      (index:=((GridTicks.index (c,j)).val:Word (64*w)))
      (params:=args) (sel:=flag z) (recv:=recv) (eval:=(D).machine) (room:=codeRoom) (i:=i))

/-- The physical compiler obligations for a fixed executable. Only the child
streams selected by the classified tick, their source translations, and
numeric cost appear in this predicate. -/
def ReceiverStreams {H J : ℕ} (src : Procedure (64*w)) (cursor control cmdBase «meta» : ℕ)
    (assembly : (D).run.Assembler (Fin I.inputSize → Bool)) : Prop :=
  ∀ (z : (D).trace) (x : GridDiagonal.Pins (Fin railCount)) c j,
    selectedStreams (pinCount:=localPins) (H:=H) (J:=J) src cursor control cmdBase «meta» machineClock
      (D).run.plan z.1 (assembly (U)) trees (rawPin x) (boundary z) (items z c j) (root z)
      (streamInput I recv raw gateBase textFits rooms widths C room z x c j)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- Instantiate the installed evaluator's `ReceiverRuns` with the physically
executed weighted product program. The only per-tick transfer here consists
of compiled child rows, their numeric translated addresses, layout and clock.
The factor list is computed by the registered resource classes on that same trace. -/
theorem runs_of_streams {H J : ℕ} (shapeFit : Fits (shape F localPins H J) (64*w))
    (src : Procedure (64*w)) (cursor control cmdBase header «meta» lut : ℕ)
    (hp : (dimensions (TraceReceiverProgram.machine shapeFit src cursor control header «meta» lut)).1≤arch)
    (hr : (dimensions (TraceReceiverProgram.machine shapeFit src cursor control header «meta» lut)).2.1≤arch)
    (hs : (dimensions (TraceReceiverProgram.machine shapeFit src cursor control header «meta» lut)).2.2≤arch)
    (installed : recv=CapacityPadding.pad (TraceReceiverProgram.machine shapeFit src cursor control header «meta» lut)
      hp hr hs)
    (large : 1024≤w) (wide : 4<2^(64*w)) (metaSpace : footprint (shape F localPins H J)≤«meta»)
    (lutSpace : footprint (shape F localPins H J)≤lut) (low : cellsBase localPins H≤«meta»)
    (rows : «meta»+4*J≤lut) (tables : lut+8*(TickTerminalPadding.tables F+2)≤header)
    (headerRoom : header+4<2^(64*w)) (ctrlRoom : control+3<2^(64*w))
    (apart : control+4≤header ∨ header+4≤control) (shiftRoom : 2+localPins+localPins<2^(64*w))
    (assembly : (D).run.Assembler (Fin I.inputSize → Bool))
    (compiled : ReceiverStreams I recv raw gateBase textFits rooms widths C room
      (H:=H) (J:=J) src cursor control cmdBase «meta» assembly) :
    ReceiverRuns I recv raw gateBase textFits rooms widths C room := by
  intro z x c j
  obtain ⟨wire,spans,price,pins,capBits,capCells,actual,clock⟩:=compiled z x c j
  have prefixBits:=stream_authentic I recv raw gateBase textFits rooms widths C room large z x c j
  let input:=streamInput I recv raw gateBase textFits rooms widths C room z x c j
  refine ⟨input,prefixBits,?_,?_⟩
  · intro i
    simp only [input,streamInput,dite_eq_left i.isLt]
  · let physicalInput : Fin I.inputSize → Bool := rawPin x
    subst recv
    have result:=TraceReceiverProgram.local_tick shapeFit src (D).run.plan z.1 (assembly (U)) trees
      physicalInput (boundary z) (items z c j) (root z) wire input pins cursor control cmdBase header
      «meta» lut spans price wide metaSpace lutSpace low rows tables headerRoom ctrlRoom apart shiftRoom
      v.fieldRoom 0 capBits capCells actual hp hr hs (v.receiverFits _) prefixBits clock
    have values := TraceReceiverSeedWords.forest_values (D).machine (D).fit (D).field (D).state
      (D).block (D).axesFit physicalInput
    exact result.trans (congrArg (fun inputFactors =>
      ((items z c j).map (fun i => (D).run.plan.cells z.1 inputFactors ((root z) i)
        (((D).run.plan.finish z.1).graph.atVertex (boundary z) ((root z) i)))).prod) values)

end Hierarchy.GridInstalledEvaluator
end

end OAI
