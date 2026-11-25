import OAI.Hierarchy.GridInstalledDistribution
import OAI.Hierarchy.GridInstalledFit

namespace OAI
/-! # The cofinal grid compiler on the installed evaluated program -/

noncomputable section
namespace Hierarchy.GridPhysicalCompiler
open ThreeFlat Diagonal Diagonal.PhysicalStage RAM
open Computability.VPVNP.BurstRAM PrivateRAM Filter GridScale TraceDistribution GridInstalledEvaluator
open scoped Classical

variable {F : Type} [Field F] [Fintype F]
variable (blk : Block F) (m degree stageRate rootRate J r : ℕ)

/-- The native tick implementation fixes a single padded machine for every
input assignment, local cell, team and successful history of this installation.
The room receipt also certifies the sum of the actual scheduled costs for that
machine, using the same factor ordering that its receiver executes. -/
def ReceiverAt {Q : ℕ→ℕ} {loss : ℕ→ℝ} {A w : ℕ}
    (v : TickSelection F (m+1) A w Q loss) (I : Installed blk m A w degree stageRate rootRate v)
    (R : GridInstalledFit.Receipt blk m A w degree stageRate rootRate v I J r) : Prop :=
  let arch:=GridDescription.capacity w
  let active:=GridInstalledEvaluator.layout m A w (overhead Q loss w) v.copies degree stageRate rootRate
  let gateBase:=26*GridDescription.sector w
  ∃ recv : Machine (64*w) arch arch arch,
    let rooms:=(R.rooms recv 0 gateBase).choose
    let width:=fun i=>(v.replacement.width_le_size i).trans v.size_le
    ∀ safe : GridNativeDispatch.WordRoom I.D,
      GridInstalledEvaluator.ReceiverRuns I recv 0 gateBase R.text rooms width
        (GridNativeDispatch.actualTable I.D safe).codes
        (GridNativeDispatch.selectorRoom I.D active R.table R.selector safe)

/-- The concrete sender, archive, positive/idle/rejected selector branches and
hardware bounds turn independent physical receiving computations into the
published grid trace.  The receiver hypothesis can specialize the kernel to
the cofinal word widths corresponding to integer physical ages. -/
theorem of_receivers (cutoff : ℕ)
    (native : ∀ A>max cutoff (UniversalTick.saving+2+(r+51)), ∀ Q loss, Envelopes Q loss →
      ∀ q : ℕ→ℕ, (∀ᶠ w : ℕ in atTop,0<q w ∧ q w≤Q w) →
        ∀ᶠ w : ℕ in atTop, ∀ t : ℕ,5120≤t → 64*w=16*t^10 → Even w →
          ∀ (v : TickSelection F (m+1) A w Q loss),v.copies=q w →
          ∀ (I : Installed blk m A w degree stageRate rootRate v)
            (R : GridInstalledFit.Receipt blk m A w degree stageRate rootRate v I J r),
            ReceiverAt blk m degree stageRate rootRate J r v I R) :
    GridTraceCompiler F (m+1) := by
  let threshold:=max cutoff (UniversalTick.saving+2+(r+51))
  refine ⟨threshold,?_⟩
  intro A saving Q loss env
  apply GridNativeShape.frequent_all (fun w (v : TickSelection F (m+1) A w Q loss)=>v.HasDistribution)
  intro x live
  let q:=fun w=>((x w).map TickSelection.copies).getD 1
  have valid : ∀ᶠ w : ℕ in atTop,0<q w ∧ q w≤Q w := by
    filter_upwards [live] with w hw
    cases hx : x w with
    | none => simp [hx] at hw
    | some v => simpa [q,hx] using And.intro v.copies_pos v.copies_le
  let u:=fun w=>evalDepth w (m+1) A 2 (overhead Q loss w) (q w)
  let reps:=fun w=>traceBlocks (m+1) (overhead Q loss w)
  have scale : Scale u reps := trace_scale env (m+1) A 2 q valid
  have tariff : UniversalTick.saving+2+(r+51)<A := (le_max_right _ _).trans_lt saving
  let coef:=GridInstalledSmall.coefficient blk degree stageRate rootRate
  apply GridNativeShape.at_physical_ages
  filter_upwards [GridInstalledEvaluator.eventual blk m A degree stageRate rootRate env q valid,
    GridInstalledFit.eventual blk m A degree stageRate rootRate env q valid J r tariff,
    GridNativeDispatch.native_write blk scale coef 2,native A saving Q loss env q valid,
    eventually_ge_atTop 1024] with w install room writer receive large
  intro t mature physical even v hx
  have chosen : v.copies=q w := by simp [q,hx]
  obtain ⟨I⟩:=install v chosen
  obtain ⟨R⟩:=room v chosen I
  obtain ⟨recv,run⟩:=receive t mature physical even v chosen I R
  let l:=layout m A w (overhead Q loss w) v.copies degree stageRate rootRate
  let gateBase:=26*GridDescription.sector w
  let rooms:=(R.rooms recv 0 gateBase).choose
  have width (i) := (v.replacement.width_le_size i).trans v.size_le
  have cpu : GridDescription.capacity w ≤ 64*w := by
    unfold GridDescription.capacity
    have := Nat.div_le_self w 1024
    omega
  have axes : I.axes+1=u w+1-w/2 := by simpa only [u,←chosen] using I.axes_eq
  obtain ⟨safe,write⟩:=writer I.D I.block_eq I.passes_eq axes cpu cpu cpu l v.replacement
    recv 0 gateBase R.text rooms width v.active R.fits R.table R.selector
  let C:=(GridNativeDispatch.actualTable I.D safe).codes
  let legal:=GridNativeDispatch.selectorRoom I.D l R.table R.selector safe
  exact GridInstalledEvaluator.distribution I recv 0 gateBase R.text rooms width C legal large
    R.fits.space.kernel R.fits.capFit write (run safe)

end Hierarchy.GridPhysicalCompiler
end

end OAI
