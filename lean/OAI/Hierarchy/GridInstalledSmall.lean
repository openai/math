import OAI.Hierarchy.GridInstalledEvaluatorSetup
import OAI.Hierarchy.GridPinArenaChosen

namespace OAI
/-! # Publisher bank room and stage prices for the self-installed image -/

namespace Hierarchy.GridInstalledSmall
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.NavigationNodeRows NodePublication TraceAdmission TraceDistribution GridRegisteredSetting
open GridScale Filter TraceFactorReceiver.Gather GridInstalledEvaluator
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Topology
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] [Fintype F]

def coefficient (blk : Block F) (degree stageRate rootRate : ℕ) :=
  let bound := blk.levels+1+degree
  4+bound+10*(bound+2)^2*stageRate+rootRate*(bound+7)

variable {w pc regs slots S base fuel axes : ℕ}
variable (D : RunData F (64*w) pc regs slots S base fuel axes (w/2)) (l : GridNativeImage.Layout)
local notation "arc" => (GridNativeImage.archive D l)
local notation "P" => (D.block.repeat D.passes)
local notation "ss" => ((P).directory (axes+1-(P).charge) (axes+1))
local notation "last" => (TraceRecovery.lastLayer (arc).K ss (arc).cursor (arc).seedLayer)
local notation "k" => (l.dimension+1)
local notation "rails" => (GridControllerSimGeometry.railCount l.dimension l.sideMinusOne l.bank)
local notation "stages" => (P).length

/-- This inequality uses the actual final record from the immutable native directory. -/
theorem root_sites : (last).count ≤ (axes+1)*2^(axes+1) := by
  have charge : (P).charge ≤ axes+1 := by rw [D.block.charge_repeat];exact D.passesFit
  have split : (P).charge+(axes+1-(P).charge)=axes+1 := by omega
  have start : (arc).seedLayer.count=(axes+1)*2^(axes+1) := rfl
  obtain ⟨row,member,stored⟩ := TraceRecovery.lastLayer_mem (arc).K ss (arc).cursor (arc).seedLayer
  have count := program_site_count P (arc).K (axes+1-(P).charge) (axes+1) (arc).cursor (arc).seedLayer
    (by rw [split,start]) row member
  rwa [stored,split] at count

/-- The four numerical inputs of the native dispatcher produced by this calculation. -/
structure Receipt (coef : ℕ) : Prop where
  small : GridPinArena.Small w (GridPinPublisher.canonical w k l.sideMinusOne l.copies l.pinWidth
    (GridNativeImage.parameterCount D l) (l.selectorCap+1) l.receiverText l.bank rails S (last).count
    (ss).length (2^(axes+1)) (2*2^(w/2))) S (2^(axes+1)) ((ss).length*2^(axes+1)) ((20*(w+1)+2)^(k+2))
  degree : 4+stages ≤ coef*(w+1)^2
  setup : setupPrice stages l.stageRate ≤ coef*(w+1)^2
  maps : mapPrice l.degree l.rootRate ≤ coef*(w+1)^2

theorem eventual (blk : Block F) {Q : ℕ → ℕ} {E : ℕ → ℝ} (env : Envelopes Q E)
    (m A degree stageRate rootRate : ℕ) (q : ℕ → ℕ) (range : ∀ᶠ w : ℕ in atTop, 0<q w ∧ q w≤Q w) :
    ∀ᶠ w : ℕ in atTop, ∀ (v : TickSelection F (m+1) A w Q E), v.copies=q w →
      ∀ i : Installed blk m A w degree stageRate rootRate v,
        Receipt i.D (layout m A w (overhead Q E w) v.copies degree stageRate rootRate)
          (coefficient blk degree stageRate rootRate) := by
  let sc := trace_scale env (m+1) A 2 q range
  have few := (tendsto_order.mp sc.blocks).2 1 (by norm_num)
  filter_upwards [GridPinArena.chosen_count blk env (m+1) A 2 (Nat.succ_pos _) q range,
    few,eventually_ge_atTop 1] with w bankRoom stageRoom large
  intro v chosen i
  let a := overhead Q E w
  let l := layout m A w a v.copies degree stageRate rootRate
  let arch := GridDescription.capacity w
  let b := pairs A w v.copies
  let count := traceBlocks (m+1) a
  let QP := i.D.block.repeat i.D.passes
  let ops := QP.directory (i.axes+1-QP.charge) (i.axes+1)
  let a₀ := GridNativeImage.archive i.D l
  let nroots := (TraceRecovery.lastLayer a₀.K ops a₀.cursor a₀.seedLayer).count
  have rows : nroots ≤ (i.axes+1)*2^(i.axes+1) := root_sites i.D l
  have axis : i.axes+1=evalDepth w (m+1) A 2 a (q w)+1-w/2 := by rw [←chosen];exact i.axes_eq
  let bankAt := fun copies : ℕ =>
    let rows := (blk.repeat count).length
    let full := 2^(i.axes+1)
    let bank := pairs A w copies
    GridPinArena.Small w (GridPinPublisher.canonical w (m+1) (side a-1) copies (pins w a)
      (GridNativeImage.parameterCount i.D l) (selector (m+1) w a) l.receiverText bank
      (external (m+1) a bank) i.inputSize nroots rows full (2*2^(w/2)))
      i.inputSize full (rows*full) (classes (m+1) w)
  have supplied : bankAt (q w) := bankRoom i.axes arch arch arch i.inputSize _ _ (GridNativeImage.parameterCount i.D l) l.receiverText
    axis i.D.axesFit i.D.machine i.D.fit nroots rows
  have seed : bankAt v.copies := (congrArg bankAt chosen).mpr supplied
  have prog : QP.length=(blk.repeat count).length := by dsimp only [QP];rw [i.block_eq,i.passes_eq]
  have steps : ops.length=(blk.repeat count).length := (Program.directory_length QP _ _).trans prog
  have cut : selector (m+1) w a-1+1=selector (m+1) w a := Nat.sub_add_cancel (Nat.two_pow_pos _)
  have arena : GridPinArena.Small w (GridPinPublisher.canonical w (m+1) (side a-1) v.copies (pins w a)
    (GridNativeImage.parameterCount i.D l) (selector (m+1) w a-1+1) l.receiverText b
    (GridControllerSimGeometry.railCount m (side a-1) b) i.inputSize nroots ops.length
    (2^(i.axes+1)) (2*2^(w/2))) i.inputSize (2^(i.axes+1)) (ops.length*2^(i.axes+1))
    (classes (m+1) w) := by rw [steps,GridInstalledEvaluator.rails,cut];exact seed
  have positive : (0:ℝ)<w := by exact_mod_cast (show 0<w by omega)
  have countBound : count ≤ w := by
    exact_mod_cast (by simpa only [one_mul] using ((div_lt_iff₀ positive).mp stageRoom).le : (count:ℝ)≤w)
  let h := blk.levels+1+degree
  have height : QP.length ≤ h*(w+1)^1 := by
    rw [prog,TraceDistribution.Physical.repeated_stages,pow_one]
    exact Nat.mul_le_mul (by dsimp only [h];omega) (by omega)
  have ports : degree ≤ h*(w+1)^1 := by
    rw [pow_one]; exact (show degree ≤ h by dsimp only [h];omega).trans (Nat.le_mul_of_pos_right _ (by omega))
  have prices := prices_polynomial w 1 h QP.length degree stageRate rootRate height ports
  let C := coefficient blk degree stageRate rootRate
  have w1 : (w+1)^1 ≤ (w+1)^2 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have dep : 4+QP.length ≤ C*(w+1)^2 := by
    have h4 := Nat.le_mul_of_pos_right 4 (Nat.pow_pos (Nat.succ_pos w) : 0 < (w+1)^2)
    have hi := height.trans (Nat.mul_le_mul_left h w1)
    calc
      _ ≤ (4+h)*(w+1)^2 := by rw [Nat.add_mul];omega
      _ ≤ _ := Nat.mul_le_mul_right _ (by dsimp [C,coefficient,h];omega)
  refine ⟨arena,dep,?_,?_⟩
  · exact prices.1.trans (Nat.mul_le_mul_right _ (by dsimp [coefficient,h];omega))
  · exact prices.2.trans (Nat.mul_le_mul (by dsimp [coefficient,h];omega) w1)

end
end Hierarchy.GridInstalledSmall

end OAI
