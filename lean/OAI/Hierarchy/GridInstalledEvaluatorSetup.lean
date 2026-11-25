import OAI.Hierarchy.GridNativeShape
import OAI.Hierarchy.GridEvaluatorHardware

namespace OAI
/-! # The selected evaluator layout, self-installation text, and measured clock -/

noncomputable section
namespace Hierarchy.GridInstalledEvaluator
open ThreeFlat Diagonal PhysicalStage RAM GridRegisteredSetting
open Computability.VPVNP.BurstRAM PrivateRAM Filter GridScale

variable {F : Type} [Field F] [Fintype F]

def layout (m A w a q degree stageRate rootRate : ℕ) : GridNativeImage.Layout :=
  let arch:=GridDescription.capacity w
  ⟨m,side a-1,pairs A w q,q,pins w a,selector (m+1) w a-1,
    SelfAdvice.textSize (64*w) arch arch,arch,10*a,degree,stageRate,rootRate⟩

theorem rails (m a B : ℕ) :
    GridControllerSimGeometry.railCount m (side a-1) B=external (m+1) a B := by
  have pos : 0 < side a := Nat.two_pow_pos _
  change (m+1)*(2*((side a-1)+1)^m*B)=(m+1)*(2*(side a)^(m+1-1)*B)
  rw [Nat.sub_add_cancel pos,Nat.add_sub_cancel]

variable (blk : Block F) {Q : ℕ→ℕ} {loss : ℕ→ℝ}
variable (m A w degree stageRate rootRate : ℕ) (v : TickSelection F (m+1) A w Q loss)
section
local notation "age" => (overhead Q loss w)
local notation "copyN" => v.copies
local notation "arch" => (GridDescription.capacity w)
local notation "l" => (layout m A w age copyN degree stageRate rootRate)
local notation "E" => (external (m+1) age (pairs A w copyN))
local notation "u" => (evalDepth w (m+1) A 2 age copyN)
local notation "base" => (E*2+SelfAdvice.textSize (64*w) arch arch)

/-- This receipt includes the equation identifying the padded evaluator with
the machine whose full weighted trace is being distributed. -/
structure Installed where
  axes : ℕ
  inputSize : ℕ
  D : RunData F (64*w) arch arch arch inputSize base (2^u) axes (w/2)
  block_eq : D.block=blk
  state_eq : D.state=0
  passes_eq : D.passes=traceBlocks (m+1) age
  axes_eq : axes+1=u+1-w/2
  input_eq : inputSize=GridSelfHeader.rawSize w E (pairs A w copyN) (GridNativeImage.parameterCount D l)
  parameters_le : GridNativeImage.parameterCount D l≤(GridStructuralHeader.coefficient blk)*(w+1)^14
  cutoff : 2^(3*w/5)≤(l).selectorCap
  capacity : GridEvaluatorHardware.FitsCapacity (GridNativeImage.machine D l v.replacement)
  installed : D.machine=CapacityPadding.pad (GridNativeImage.machine D l v.replacement)
    capacity.1 capacity.2.1 capacity.2.2
  extra : ℕ
  clock_eq : ((extra+GridNativeEvaluator.tailTime (e:=E) (n:=side age-1) v.replacement+
    GridNativeImage.emissionTime D l)+4+5*((l).selectorCap+1))=2^u
end

set_option maxHeartbeats 800000 in
private theorem installed_text {w S mount fuel axes : ℕ}
    (D₀ : RunData F (64*w) (GridDescription.capacity w) (GridDescription.capacity w)
      (GridDescription.capacity w) S mount fuel axes (w/2)) (l : GridNativeImage.Layout)
    (X : Catalyst.Approximation F (l.dimension+1) (l.copies*l.pinWidth))
    (cap : GridEvaluatorHardware.FitsCapacity (w:=w) (p:=(9+(GridNativeImage.emitter D₀ l).labels)+35)
      (r:=(GridNativeImage.emitter D₀ l).registers+10) (k:=(GridNativeImage.emitter D₀ l).slots+5)
      (GridNativeImage.machine D₀ l X))
    (M : Machine (64*w) (GridDescription.capacity w) (GridDescription.capacity w) (GridDescription.capacity w))
    (fit : NativeTrace.Fits M S mount ((axes+1)+w/2) fuel)
    (mounted : M=CapacityPadding.pad (GridNativeImage.machine D₀ l X) cap.1 cap.2.1 cap.2.2) :
    let D := GridNativeImage.replace D₀ M fit
    ∀ newCap : GridEvaluatorHardware.FitsCapacity (GridNativeImage.machine D l X),
      D.machine=CapacityPadding.pad (GridNativeImage.machine D l X) newCap.1 newCap.2.1 newCap.2.2 := by
  intro D newCap
  exact mounted.trans (congrArg (fun m => CapacityPadding.pad m cap.1 cap.2.1 cap.2.2)
    (GridNativeImage.text_fixed D₀ l M fit X).symm)

set_option maxHeartbeats 800000 in
private theorem charged_time (env : Envelopes Q loss) {depthPath blocksPath : ℕ → ℕ}
    (scale : TraceDistribution.Scale depthPath blocksPath) :
    ∀ᶠ w : ℕ in atTop, ∀ (v : TickSelection F (m+1) A w Q loss),
      let a := overhead Q loss w
      let arch := GridDescription.capacity w
      let n := side a-1
      let B := pairs A w v.copies
      let e := external (m+1) a B
      let l := layout m A w a v.copies degree stageRate rootRate
      ∀ {S mount fuel k : ℕ} (D : RunData F (64*w) arch arch arch S mount fuel k (w/2)),
        D.block = blk → D.passes = blocksPath w → k+1 = depthPath w+1-w/2 →
        S = GridSelfHeader.rawSize w e B (GridNativeImage.parameterCount D l) →
        GridNativeEvaluator.tailTime (n := n) (e := e) v.replacement +
          GridNativeImage.emissionTime D l+4+5*(l.selectorCap+1) ≤
            2^(evalDepth w (m+1) A 2 a v.copies) := by
  filter_upwards [GridEvaluatorHardware.installed_clock env blk scale m A] with w clock
  intro v
  dsimp only
  intro S mount fuel k D blockEq passesEq axes exactInput
  let a := overhead Q loss w
  let arch := GridDescription.capacity w
  let n := side a-1
  let B := pairs A w v.copies
  let e := external (m+1) a B
  let l := layout m A w a v.copies degree stageRate rootRate
  have dims : arch≤64*w := (Nat.div_le_self w 1024).trans (by omega)
  have ord : n+1=side a := Nat.sub_add_cancel (Nat.two_pow_pos _)
  have railCount : GridControllerSimGeometry.railCount m n B=e := rails m a B
  have inputOnRails : S=GridSelfHeader.rawSize w (GridControllerSimGeometry.railCount m n B) B
      (GridNativeImage.parameterCount D l) := by
    rw [railCount]
    exact exactInput
  have room:=clock v.copies v.copies_pos v.copies_le D blockEq passesEq axes dims dims dims
    n (SelfAdvice.textSize (64*w) arch arch) arch (10*a) degree stageRate rootRate ord
    inputOnRails v.replacement v.size_le
  have one : 0 < selector (m+1) w a := Nat.two_pow_pos _
  have selectors : l.selectorCap+1=selector (m+1) w a := Nat.sub_add_cancel one
  have endTime:=room.trans (Nat.lt_log2_self (n:=evalWork w (m+1) A 2 a v.copies)).le
  change GridNativeEvaluator.tailTime (e:=GridControllerSimGeometry.railCount m n B) (n:=n) v.replacement+
      GridNativeImage.emissionTime D l+4+5*selector (m+1) w a≤2^(evalDepth w (m+1) A 2 a v.copies) at endTime
  rw [railCount] at endTime
  change GridNativeEvaluator.tailTime (n := n) (e := e) v.replacement +
    GridNativeImage.emissionTime D l + 4 + 5 * (l.selectorCap+1) ≤
      2^(evalDepth w (m+1) A 2 a v.copies)
  rw [selectors]
  exact endTime

end Hierarchy.GridInstalledEvaluator
end

end OAI
