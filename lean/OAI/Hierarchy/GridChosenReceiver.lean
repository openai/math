import OAI.Hierarchy.GridFullReceiverHardware
import OAI.Hierarchy.GridReceiverBanks
import OAI.Hierarchy.GridReceiverLayoutScale
import OAI.Hierarchy.TraceReceiverLeafSetup
import OAI.Hierarchy.TraceReceiverInstalled

namespace OAI
/-! # The one receiving program installed on all cells of the diagonal -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.GridChosenReceiver

open ThreeFlat Diagonal PhysicalStage RAM Computability.VPVNP.BurstRAM PrivateRAM
open TickWeightedBank Contraction BitLayout PhysicalProcedure
open TraceDistribution GridScale GridRegisteredSetting GridInstalledEvaluator GridPhysicalCompiler Filter
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {w pc rr pp size base fuel axes : ℕ}
variable (D : RunData F (64*w) pc rr pp size base fuel axes (w/2)) (l : GridNativeImage.Layout)
local notation "W" => (64*w)
local notation "V" => TraceAdmission.receiverAge w
local notation "dir" => GridReceiverDirectory.native D l
local notation "pars" => (dir).parameters
local notation "nroots" => (pars).roots
local notation "period" => ((l.sideMinusOne+1)^(l.dimension+1)*l.copies)
local notation "text" => SelfAdvice.textSize W pc pp

/-- The RAM instruction sequence and all its public operands have been fixed
by the dimensions and the original evaluator. They are shared by every tick
and all possible input tapes. -/
def source : Procedure W :=
  TraceReceiverProgram.fullSource D.block w V text (GridNativeImage.parameterCount D l)
    nroots ((l.dimension+1)+2) period dir (pars).firstFinal
    (TraceReceiverLeafSetup.start w) (TraceReceiverLeafSetup.pages w)
    (TraceReceiverLeafSetup.templateSrc D l) (TraceReceiverLeafSetup.gateBase D)
    (TraceReceiverLeafSetup.templateSize D) (axes+1) (w/2)
    (TraceReceiverLeafSetup.dict D) (TraceReceiverLeafSetup.masks D) (TraceReceiverLeafSetup.tmp D)
    (TraceReceiverLeafSetup.bank D l) (TraceReceiverLeafSetup.shape D) (TraceReceiverLeafSetup.rom D)
    (TraceReceiverLeafSetup.rest D) (GridReceiverBanks.pinPlan D l) (TraceReceiverLeafSetup.intervalBase w)
    (GridReceiverBanks.limit w) (GridReceiverBanks.tasks w) (GridReceiverBanks.arena D l)
    (GridReceiverBanks.mapHeader w) (GridReceiverBanks.commands w) (GridReceiverBanks.cursor w)
    (GridReceiverBanks.width w)

local notation "H" => (UniversalTick.clock w UniversalTick.saving/40000)
local notation "C" => (2*H)
local notation "sec" => TickWorkspace.base V

def program (fit : Fits (shape F l.pinWidth H C) W) :=
  TraceReceiverProgram.machine fit (source D l) (GridReceiverBanks.cursor w)
    (sec 18) (sec 18+48) (sec 9) (sec 10)

theorem eventual_capacity (B : Block F) : ∀ᶠ w : ℕ in atTop,∀ {pc rr pp size base fuel axes : ℕ}
    (D : RunData F (64*w) pc rr pp size base fuel axes (w/2)) (l : GridNativeImage.Layout),
    D.block=B → ∀ fit,GridEvaluatorHardware.FitsCapacity (program D l fit) := by
  filter_upwards [TraceReceiverProgram.full_machine_capacity B] with w sized
  intro pc rr pp size base fuel axes D l same fit
  rcases GridReceiverDirectory.hardware_fields D l with ⟨alpha,degree,ch,ha,mo⟩
  rw [←same] at sized
  apply sized <;> assumption

section Installed

variable {blk : Block F} {m A degree stageRate rootRate J r : ℕ} {Q : ℕ→ℕ} {loss : ℕ→ℝ}
    {v : TickSelection F (m+1) A w Q loss}
    (I : Installed blk m A w degree stageRate rootRate v)
    (R : GridInstalledFit.Receipt blk m A w degree stageRate rootRate v I J r)

local notation "l₀" => (layout m A w (overhead Q loss w) v.copies degree stageRate rootRate)
local notation "D₀" => I.D
local notation "N" => (l₀).pinWidth

/-- The remaining operational statement for the actual receiver. It requests
the compiled four-word rows and their input translations at the unpadded map
of the selected trees, including the number of real instructions that issued
them. All bytecode, input words, addresses and chosen trees are fixed here. -/
def Compiled : Prop :=
  ∀ (fit : Fits (shape F N H C) W) (cap : GridEvaluatorHardware.FitsCapacity (program D₀ l₀ fit)),
    let recv:=CapacityPadding.pad (program D₀ l₀ fit) cap.1 cap.2.1 cap.2.2
    let gateBase:=26*GridDescription.sector w
    let rooms:=(R.rooms recv 0 gateBase).choose
    let widths:=fun i=>(v.replacement.width_le_size i).trans v.size_le
    ∀ safe : GridNativeDispatch.WordRoom D₀,
      ReceiverStreams I recv 0 gateBase R.text rooms widths (GridNativeDispatch.actualTable D₀ safe).codes
        (GridNativeDispatch.selectorRoom D₀ l₀ R.table R.selector safe) («H»:=H) (J:=C)
        (source D₀ l₀) (GridReceiverBanks.cursor w) (sec 18) (GridReceiverBanks.commands w)
        (sec 9) (receiverAssembly I)

/-- All capacities, literal root count, pin/table addresses and public RAM
program choices in the diagonal follow from uniform architecture and the
dyadic workspace inequalities. -/
theorem eventual_receiver (blk : Block F) :
    ∀ᶠ w : ℕ in atTop,∀ {m A degree stageRate rootRate J r : ℕ}
      {Q : ℕ→ℕ} {loss : ℕ→ℝ} {v : TickSelection F (m+1) A w Q loss}
      (I : Installed blk m A w degree stageRate rootRate v)
      (R : GridInstalledFit.Receipt blk m A w degree stageRate rootRate v I J r),
      Compiled I R → ReceiverAt blk m degree stageRate rootRate J r v I R := by
  let fixed:=max (Fintype.card F*Fintype.card F) (8*(TickTerminalPadding.tables F+2))
  filter_upwards [GridReceiverClock.workspace_pages fixed,eventual_capacity blk,
    eventually_ge_atTop 1024] with w pages hardware large
  intro m A degree stageRate rootRate J r Q loss v I R compiled
  let scale:=overhead Q loss w
  let scene:=layout m A w scale v.copies degree stageRate rootRate
  obtain ⟨stride,pins,clock,total,top⟩:=pages scale
  have field:= (Nat.le_max_left _ _).trans total
  have tables:= (Nat.le_max_right _ _).trans total
  obtain ⟨fit,metadata,lut,frame,rows,tablesFit,head,ctrl,apart,shift⟩:=
    GridPhysicalCompiler.workspace (p:=scene.pinWidth) (fuel:=UniversalTick.clock w UniversalTick.saving)
      F stride pins clock field tables top
  have cap:=hardware I.D scene I.block_eq fit
  have wide : 4<2^(64*w) := by
    have p:=Nat.pow_le_pow_right (n:=2) (by decide) (show 3≤64*w by omega)
    exact lt_of_lt_of_le (by decide : 4<2^3) p
  exact receiverAt_of_streams I R fit (source I.D scene) (GridReceiverBanks.cursor w)
    (TickWorkspace.base (TraceAdmission.receiverAge w) 18) (GridReceiverBanks.commands w)
    (TickWorkspace.base (TraceAdmission.receiverAge w) 18+48)
    (TickWorkspace.base (TraceAdmission.receiverAge w) 9) (TickWorkspace.base (TraceAdmission.receiverAge w) 10)
    large cap.1 cap.2.1 cap.2.2 wide metadata lut frame rows tablesFit head ctrl (Or.inl apart) shift
    (compiled fit cap)

end Installed

/-- Deduce the grid compiler directly from the native prepared-stream
execution on the single fixed program above. The choice of a width or a
successful selector never changes its instructions. -/
theorem of_compiled (blk : Block F) (m degree stageRate rootRate J r cutoff : ℕ)
    (compiled : ∀ A>max cutoff (UniversalTick.saving+2+(r+51)), ∀ Q loss, Envelopes Q loss →
      ∀ q : ℕ→ℕ, (∀ᶠ w : ℕ in atTop,0<q w ∧ q w≤Q w) →
        ∀ᶠ w : ℕ in atTop, ∀ t : ℕ,5120≤t → 64*w=16*t^10 → Even w →
          ∀ (v : TickSelection F (m+1) A w Q loss),v.copies=q w →
          ∀ (I : Installed blk m A w degree stageRate rootRate v)
            (R : GridInstalledFit.Receipt blk m A w degree stageRate rootRate v I J r),
            Compiled I R) : GridTraceCompiler F (m+1) := by
  apply GridPhysicalCompiler.of_receivers blk m degree stageRate rootRate J r cutoff
  intro A saving Q loss env q valid
  filter_upwards [eventual_receiver blk,compiled A saving Q loss env q valid] with w room exec
  intro t mature term even v copies I R
  exact room I R (exec t mature term even v copies I R)

end Hierarchy.GridChosenReceiver
end

end OAI
