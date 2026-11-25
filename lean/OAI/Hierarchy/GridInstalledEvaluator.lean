import OAI.Hierarchy.GridInstalledEvaluatorSetup

namespace OAI
/-! # A self-installed evaluator with its authentic RAM clock and input image -/

noncomputable section
namespace Hierarchy.GridInstalledEvaluator
open ThreeFlat Diagonal PhysicalStage RAM GridRegisteredSetting
open Computability.VPVNP.BurstRAM PrivateRAM Filter GridScale

variable {F : Type} [Field F] [Fintype F]

open private installed_text charged_time from OAI.Hierarchy.GridInstalledEvaluatorSetup

variable (blk : Block F) {Q : ℕ→ℕ} {loss : ℕ→ℝ}
variable (m A w degree stageRate rootRate : ℕ) (v : TickSelection F (m+1) A w Q loss)

set_option maxHeartbeats 1000000 in
/-- A trajectory is used only to establish the uniform asymptotic trace scale.
At each selected volume the architecture is immutable and the machine is
constructed from its public shape, its chosen X and the fixed stage block. -/
theorem eventual (env : Envelopes Q loss) (q : ℕ→ℕ)
    (range : ∀ᶠ w : ℕ in atTop,0<q w ∧ q w≤Q w) :
    ∀ᶠ w : ℕ in atTop, ∀ (v : TickSelection F (m+1) A w Q loss),v.copies=q w→
      Nonempty (Installed blk m A w degree stageRate rootRate v) := by
  let u' := fun w=>evalDepth w (m+1) A 2 (overhead Q loss w) (q w)
  let stages := fun w=>traceBlocks (m+1) (overhead Q loss w)
  have scale := trace_scale env (m+1) A 2 q range
  filter_upwards [GridNativeShape.choose blk env (m+1) A 2 (Nat.succ_pos _),
    GridEvaluatorHardware.installed blk,charged_time blk m A degree stageRate rootRate env scale,
    TraceDistribution.native_fits (F:=F) scale 1 0 0 (by decide),
    TraceDistribution.lane_room scale blk.blockCharge] with w shape hardware clock bounds pass
  intro v chosen
  let a:=overhead Q loss w
  let k:=u' w+1-w/2-1
  let arch:=GridDescription.capacity w
  let n:=side a-1
  let B:=pairs A w v.copies
  let e:=external (m+1) a B
  let mount:=e*2+SelfAdvice.textSize (64*w) arch arch
  let l:=layout m A w a v.copies degree stageRate rootRate
  have size : 2≤u' w+1-w/2 := bounds.2.1
  have axes : k+1=u' w+1-w/2 := Nat.sub_add_cancel (by omega)
  have hk : 2≤k+1 := axes ▸ size
  have hi : w/2≤u' w := bounds.2.2.1
  have eqn : k+1+w/2=evalDepth w (m+1) A 2 a v.copies+1 := by rw [chosen];change k+1+w/2=u' w+1;omega
  obtain ⟨S,N,raw,count,below,cut,guard,bits,fits⟩:=
    shape v.copies v.copies_pos v.copies_le eqn
  let blank := UniversalTick.accept (64*w) arch arch arch v.active
  obtain ⟨first,firstN⟩:=fits blank
  let D0 : RunData F (64*w) arch arch arch S mount (2^(evalDepth w (m+1) A 2 a v.copies)) k (w/2) :=
    ⟨blank,first,v.fieldRoom,0,blk,hk,stages w,by rw [axes];exact pass⟩
  have hard:=hardware D0 l rfl v.replacement
  let ev:=CapacityPadding.pad (GridNativeImage.machine D0 l v.replacement) hard.1 hard.2.1 hard.2.2
  obtain ⟨fit,fullN⟩:=fits ev
  let D:=GridNativeImage.replace D0 ev fit
  have installedCapacity:=hardware D l rfl v.replacement
  have ct : N=GridNativeImage.parameterCount D l := fullN v.fieldRoom
  have exactInput : S=GridSelfHeader.rawSize w e B (GridNativeImage.parameterCount D l) := raw.trans (congrArg _ ct)
  let t:=GridNativeEvaluator.tailTime (e:=e) (n:=n) v.replacement+GridNativeImage.emissionTime D l+4+5*(l.selectorCap+1)
  have fee : t≤2^(evalDepth w (m+1) A 2 a v.copies) :=
    clock v D rfl rfl axes exactInput
  have fill (x y s budget : ℕ) (bound : x+y+4+5*(s+1)≤budget) :
      ((budget-(x+y+4+5*(s+1))+x+y)+4+5*(s+1))=budget := by omega
  have params : GridNativeImage.parameterCount D l ≤ GridStructuralHeader.coefficient blk*(w+1)^14 :=
    ct.symm.trans_le count
  have axisCount : k+1=evalDepth w (m+1) A 2 a v.copies+1-w/2 := by rw [chosen];exact axes
  refine ⟨⟨k,S,D,rfl,rfl,rfl,axisCount,exactInput,params,cut,installedCapacity,
    installed_text D0 l v.replacement hard ev fit rfl installedCapacity,
    2^(evalDepth w (m+1) A 2 a v.copies)-t,?_⟩⟩
  · exact fill (GridNativeEvaluator.tailTime (e:=e) (n:=n) v.replacement)
      (GridNativeImage.emissionTime D l) l.selectorCap (2^(evalDepth w (m+1) A 2 a v.copies)) fee

end Hierarchy.GridInstalledEvaluator
end

end OAI
