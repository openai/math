import OAI.Hierarchy.GridInstalledEvaluator
import OAI.Hierarchy.GridNativeDispatch
import OAI.Hierarchy.GridMountedDistribution
import OAI.Hierarchy.GridTickInstalled
import OAI.Hierarchy.FlatDiagonal

namespace OAI
/-! # Interpreting the installed evaluator and receiver on one selection -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy
open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open RAM Computability.VPVNP.BurstRAM PrivateRAM UniversalGrid TraceDistribution GridThrough GridScale GridRegisteredSetting
open scoped Classical BigOperators
variable {F : Type} [Field F] [Fintype F] {Q : ℕ→ℕ} {loss : ℕ→ℝ}

namespace TickSelection
theorem distribution_of_shape {k A w e cap : ℕ} (v : TickSelection F k A w Q loss)
    (rails : e=external k (overhead Q loss w) (pairs A w v.copies))
    (size : cap+1=selector k w (overhead Q loss w))
    (dir : Fin e→Fin k)
    (ctrl : Bits (w^2) → Bits (cap+1) → Option (Setting v.replacement (side (overhead Q loss w)-1) e dir))
    (code : Bits (w^2)) (actual : (grid v.network v.replacement dir ctrl).Distributed code) :
    v.HasDistribution := by
  unfold HasDistribution
  dsimp only
  rw [←rails,←size]
  exact ⟨dir,ctrl,code,⟨actual⟩⟩

end TickSelection

namespace GridInstalledEvaluator
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
local notation "ctrl" => honestController (D).run.plan C grades chosen code
local notation "tape" => (fun x : GridDiagonal.Pins (Fin railCount) =>
  GridDescription.input (x ∘ Wiring.railPin.symm) code suffix)
local notation "seed" => (fun x : GridDiagonal.Pins (Fin railCount) =>
  Physical.seed (D).block (D).axesFit (TraceDistribution.layout (D).machine (D).fit (D).field (D).state)
    (fun j => tape x j.val))
local notation "cost" => (fun z : (D).trace => (D).costs (GridNativeImage.resources D l) z.1 m n B
  (D).issuedCharges ((D).issuedUnit w degree stageRate rootRate))

/-- The receiver's local computation takes place on the physical external and
literal pins actually selected by the installed writer. It sees the same
padded program at address zero for each selected cell and team. -/
def ReceiverRuns : Prop :=
  ∀ (z : (D).trace) (x : GridDiagonal.Pins (Fin railCount)) c j,
    ∃ input : ℕ→Bool,
      (∀ i,input i.val=NativeTrace.executable recv i) ∧
      (∀ i : Fin (l).pinWidth,input i.val=(chosen (some z)).1.dataBits x c (finProdFinEquiv (j,i))) ∧
      (NativeTrace.network recv (v.receiverFits recv) v.fieldRoom 0).eval
        (TraceBitHeader.advicePins 0 (NativeTrace.executable recv) input) =
        ((FactorAllocation.factors w (cost z) (List.ofFn id) (GridTicks.index (c,j))).map
          (fun i => cellFactor (D).run.plan grades (GridPhysicalSelector.siteOrder (D).run)
            (D).run.terminalLabels seed z i x)).prod

/-- The two actual executions use the same serialized code, physical history
and terminal site order. -/
theorem distribution (large : 1024≤w)
    (memory : GridNativeEvaluator.footprint («n»:=n) (e:=railCount) X≤2^(64*w))
    (capBound : cap<GridDescription.sector w)
    (write : GridNativeDispatch.Writes D l X recv raw gateBase textFits rooms widths v.active C room)
    (runs : ReceiverRuns I recv raw gateBase textFits rooms widths C room) : v.HasDistribution := by
  have rail := rails m age B
  have ell : cap+1=selector (m+1) w age := Nat.sub_add_cancel (Nat.two_pow_pos _)
  have upper := GridDescription.sectors_fit (by omega : 0<w)
  have address : 12*GridDescription.sector w+(cap+1)<2^(64*w) := by omega
  have codeFits := GridDescription.room (w:=w) large
    (p:=arch) (k:=arch) (p':=arch) (k':=arch) le_rfl le_rfl le_rfl le_rfl
  let durationAt := fun railTotal : ℕ =>
    I.extra + GridNativeEvaluator.tailTime («n»:=n) (e:=railTotal) X +
      GridNativeImage.emissionTime D l + 4 + 5*(cap+1)
  apply v.distribution_of_shape rail ell dir ctrl code
  apply mounted_distribution v.network X dir recv (GridNativeImage.emitter D l) (D).field
    I.capacity.1 I.capacity.2.1 I.capacity.2.2 (D).machine I.extra (D).fit (D).state
    (D).block (D).axesFit (D).passes (D).passesFit C suffix chosen I.installed
    (congrArg (fun e : ℕ => e*2+SelfAdvice.textSize (64*w) arch arch) rail.symm)
    (I.clock_eq.symm.trans (congrArg durationAt rail.symm)) memory address codeFits room
    (fun _ => rfl) (fun c => GridIdleLayout.ticks_one v.active v.tickFit v.fieldRoom 0
      (X).width widths (fun _=>false) c) (fun _ _ => by change some _ ≠ none; simp)
    v.copies_pos w cost write
  intro z x c j
  obtain ⟨input,prefixBits,slice,computed⟩ := runs z x c j
  have read := v.receiver_value recv input _ prefixBits computed
  have same : (fun i : Fin (l).pinWidth => input i.val) =
      (fun i => (chosen (some z)).1.dataBits x c (finProdFinEquiv (j,i))) := funext slice
  exact (congrArg v.network.eval same).symm.trans read

end GridInstalledEvaluator
end Hierarchy
end

end OAI
