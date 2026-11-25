import OAI.Hierarchy.GridChosenReceiver
import OAI.Hierarchy.GridChosenReceiverPrice
import OAI.Hierarchy.TraceReceiverCopyAdmission

namespace OAI
/-! # Charging the actual receiving setup at the installed widths -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.GridChosenReceiver

open ThreeFlat Diagonal PhysicalStage RAM NavigationPass NavigationDirectory
open Computability.VPVNP.BurstRAM PrivateRAM TraceDistribution TraceAdmission GridRegisteredSetting
open GridScale GridInstalledEvaluator Filter

variable {F : Type} [Field F] [Fintype F] {w pc rr pp size base fuel axes : ℕ}
variable (D : RunData F (64*w) pc rr pp size base fuel axes (w/2)) (l : GridNativeImage.Layout)
local notation "dir" => (GridReceiverDirectory.native D l)
local notation "p" => (dir).parameters
local notation "K" => (2^(3*w/5) : ℕ)

/-- Covers setup through registered independent classifier, both selected
root scans and the initialization of the terminal row job. -/
def setupTime : ℕ :=
  2*GridReceiverClock.startupTime w l.pinWidth K (p).roots ((l.dimension+1)+2)
      (dir).archive (dir).stages (dir).edges+
    GridReceiverClock.scans w (HistoryStageBody.Physical.libraryWords D.block (64*w))
      (TraceReceiverLeafSetup.templateSize D) (axes+1) (w/2) (TraceReceiverLeafSetup.dict D)
      (TraceReceiverLeafSetup.masks D) (p).firstFinal (p).roots (GridReceiverBanks.pinPlan D l)

theorem eventual_setup (B : Block F) (m A degree stageRate rootRate margin : ℕ)
    {Q : ℕ→ℕ} {loss : ℕ→ℝ} (env : Envelopes Q loss) (q : ℕ→ℕ)
    (valid : ∀ᶠ w : ℕ in atTop,0<q w ∧ q w≤Q w) :
    ∀ᶠ w : ℕ in atTop,∀ v : TickSelection F (m+1) A w Q loss,v.copies=q w →
      ∀ I : Installed B m A w degree stageRate rootRate v,
        margin*setupTime I.D (layout m A w (overhead Q loss w) v.copies degree stageRate rootRate)
          ≤UniversalTick.clock w UniversalTick.saving := by
  let k:=m+1
  let u:=fun w=>evalDepth w k A 2 (overhead Q loss w) (q w)
  let reps:=fun w=>traceBlocks k (overhead Q loss w)
  have scale : Scale u reps:=trace_scale env k A 2 q valid
  let coeff:=GridStructuralHeader.coefficient B
  filter_upwards [GridReceiverClock.setup_clock env k A (k+2) coeff margin,
    eventual_receiver_directory_count B scale,TraceAdmission.terminal_edges B scale,
    GridReceiverClock.tick_count env k,record_room scale 1,
    (tendsto_order.mp scale.cap).2 2 (by norm_num),valid,eventually_ge_atTop 2] with
      w price nodes edges schedule volume close copies large
  intro v eqn I
  let a:=overhead Q loss w
  let layout':=layout m A w a v.copies degree stageRate rootRate
  let D:=I.D
  let d:=GridReceiverDirectory.native D layout'
  let capacityCutoff : ℕ := 2^(3*w/5)
  have axes : I.axes+1=u w+1-w/2 := by simpa only [u,k,←eqn] using I.axes_eq
  have stageEq : D.passes=reps w:=I.passes_eq
  have fit : B.blockCharge*reps w≤I.axes+1 := by
    have chargeEq : D.block.blockCharge * D.passes = B.blockCharge * reps w :=
      congrArg₂ (fun (block : Block F) (n : ℕ) => block.blockCharge*n) I.block_eq stageEq
    exact chargeEq.ge.trans D.passesFit
  have first := nodes (I.axes+1) axes fit d.archive.K d.archive.cursor d.archive.seedLayer rfl rfl rfl
  have edge := edges (I.axes+1) axes fit
  have firstFit : d.parameters.firstFinal+d.parameters.roots≤capacityCutoff := by
    change receiverDirectoryCount d.archive.K d.stages d.archive.cursor d.archive.seedLayer≤capacityCutoff
    let count (block : Block F) (n : ℕ) : ℕ :=
      let plan := block.repeat n
      receiverDirectoryCount d.archive.K (plan.directory (I.axes+1-plan.charge) (I.axes+1))
        d.archive.cursor d.archive.seedLayer
    exact (congrArg₂ count I.block_eq stageEq).le.trans first
  have edgeFit : d.edges≤capacityCutoff := by
    let size (block : Block F) (n : ℕ) : ℕ :=
      let plan := block.repeat n
      plan.finalEdges (I.axes+1-plan.charge) (I.axes+1)
    exact (congrArg₂ size I.block_eq stageEq).le.trans edge
  have scaleFit : (d.archive).pairCapacity≤GridScale.pins w a := by
    change GridScale.selector k w a-1≤GridScale.pins w a
    apply (Nat.sub_le ..).trans
    unfold GridScale.selector GridScale.pins
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_right a (by omega : 4≤10*k+24)) w
  have packed : HistoryStageBody.Physical.libraryWords D.block (64*w)+TraceReceiverLeafSetup.templateSize D
      ≤coeff*(w+1)^14 := by
    have bounded (dirs template lib : ℕ) : lib+template ≤
        GridStructuralHeader.wordCount dirs template lib := by
      unfold GridStructuralHeader.wordCount
      omega
    exact (bounded (GridStructuralHeader.directory (w:=w) D.block (I.axes+1)
      D.passes layout'.selectorCap).length (TraceReceiverLeafSetup.templateSize D)
      (HistoryStageBody.Physical.libraryWords D.block (64*w))).trans I.parameters_le
  have height : I.axes+1+w/2≤64*w := by
    have hw : (0:ℝ)<w := by exact_mod_cast (by omega : 0<w)
    have rate : (u w:ℝ)<2*w := (div_lt_iff₀ hw).mp close
    have nrate : u w<2*w := by exact_mod_cast rate
    omega
  have slots : 2^(I.axes+1)≤capacityCutoff := by
    rw [←axes] at volume
    change 2^(I.axes+1)≤2^(3*w/5)
    have one : 1≤I.axes+1 := by omega
    have seed := Nat.mul_le_mul_right (2^(I.axes+1)) one
    have factor : 1≤reps w+1 := by omega
    have full := Nat.mul_le_mul_right (1+(I.axes+1)*2^(I.axes+1)) factor
    have last := Nat.mul_le_mul_left ((reps w+1)*(1+(I.axes+1)*2^(I.axes+1)))
      (show 1≤64*w+1 by omega)
    simp only [Nat.one_mul,Nat.mul_one] at seed full volume last
    omega
  have tickOrder : (GridReceiverBanks.pinPlan D layout').ticks=ticks k a (q w) := by
    change (side a-1+1)^k*v.copies=_
    have sidePositive : 1 ≤ side a := Nat.two_pow_pos _
    rw [Nat.sub_add_cancel sidePositive,eqn]
    rfl
  apply price (q w) copies.1 copies.2 d.archive d.stages d.parameters.roots d.edges
    d.parameters.firstFinal (HistoryStageBody.Physical.libraryWords D.block (64*w))
    (TraceReceiverLeafSetup.templateSize D) (I.axes+1) (w/2) (TraceReceiverLeafSetup.dict D)
    (TraceReceiverLeafSetup.masks D) (GridReceiverBanks.pinPlan D layout')
    firstFit edgeFit scaleFit packed height
  · rw [tickOrder]
    exact schedule (q w) copies.2
  · rfl
  · have inputFit : I.inputSize ≤ 2^(I.axes+1)*(2*2^(w/2)) := by
      rw [show 2^(I.axes+1)*(2*2^(w/2))=2^(1+((I.axes+1)+w/2)) by
        rw [pow_add,pow_add]; ring]
      exact (Nat.le_add_right ..).trans I.D.fit.grid
    have countLanes (size full span : ℕ) (pos : 0<span) (fits : size≤full*span) :
        (size+span-1)/span ≤ full := by
      apply Nat.le_of_lt_succ
      apply (Nat.div_lt_iff_lt_mul pos).mpr
      rw [Nat.succ_mul]
      omega
    exact (countLanes _ _ _ (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) inputFit).trans slots

end Hierarchy.GridChosenReceiver
end

end OAI
