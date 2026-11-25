import OAI.ThreeFlat.Diagonal.PhysicalSelectedClock
import OAI.ThreeFlat.Diagonal.PhysicalSelectedStorage
import OAI.ThreeFlat.Diagonal.PhysicalVisitRates
import OAI.ThreeFlat.Diagonal.PhysicalRefreshLocalPrices
import OAI.ThreeFlat.Diagonal.PhysicalTreeResources
import OAI.ThreeFlat.RAM.HistoryStageResources
import OAI.ThreeFlat.Diagonal.PhysicalRefreshAssembly
import OAI.ThreeFlat.Diagonal.PhysicalRefreshOutput
import OAI.ThreeFlat.Diagonal.TraceSeedResources
import OAI.ThreeFlat.RAM.HistoryMotifRates
import OAI.ThreeFlat.Diagonal.HistoryPhysicalStages
import OAI.ThreeFlat.Diagonal.PhysicalRegisterSpace
import OAI.ThreeFlat.Diagonal.TickTotalBudget
import OAI.ThreeFlat.Diagonal.PhysicalIndividualCharge
import OAI.ThreeFlat.RAM.TickTerminalRoot

namespace OAI
/-! # Fixed-degree work bound for the selected physical H forest -/

noncomputable section
namespace ThreeFlat.Diagonal.PhysicalStage.Block
open HistoryContraction RAM RAM.HistoryStageBody
open private leafRuntimeRate_eq from OAI.ThreeFlat.RAM.HistoryStageTariff
open scoped Classical BigOperators
noncomputable section
variable {F Pins : Type} [Field F] [Fintype F] (B : Block F) {u : ℕ}

/-- The same S43 numerical unit pays the weighted-matrix padding test before
a time slot or native memory image is selected. -/
theorem weighted_rows_le_archiveUnit (degree c : ℕ) :
    10000*B.terminalRowRate u c≤B.archiveUnit u c degree := by
  let levels:=(B.repeat (u^8)).length
  let k:= c*(16*u^10+1)^3
  have leafFloor (v : ℕ) : 10000 ≤ 400063 + 12*v :=
    (by decide : 10000 ≤ 400063).trans (Nat.le_add_right ..)
  have budgetFloor (leaf kernel roots guardFee pages : ℕ) (paid : 10000 ≤ leaf) :
      10000 ≤ 1+leaf+kernel+6*roots+guardFee+pages := by omega
  have coef : 10000 ≤ B.stageClockRate :=
    budgetFloor Physical.leafRuntimeRate (Physical.blockKernelRate B) (Physical.blockRootRate B)
      (Physical.blockGuardFee B) (Physical.blockPageRate B)
      ((leafFloor (2*(HistorySelectedOps.tariff [] + 3*Physical.rawLeafBinds)+4)).trans_eq leafRuntimeRate_eq)
  have depthBound (n : ℕ) : 2*n+1 ≤ 10*(n+2)^2 := by
    nlinarith [Nat.zero_le (n^2)]
  have moveFactors (n k : ℕ) : 10000*((2*n+1)*k) = (2*n+1)*10000*k := by ring
  have bound := Nat.mul_le_mul (depthBound levels) coef
  calc
    10000*B.terminalRowRate u c = (2*levels+1)*10000*k := moveFactors levels k
    _ ≤ B.stageUnit u c := Nat.mul_le_mul_right k bound
    _ ≤ B.archiveUnit u c degree:=Nat.le_add_right ..

theorem typed_root_admission {rem : ℕ} (A : State (2^B.exponent 0) ((B.repeat (u^8)).charge+rem))
    (h : ((B.repeat (u^8)).run rem A).plan.History)
    (J : Run.WordSteps Pins ((B.repeat (u^8)).run rem A)) (L : A.Words Pins)
    (ord : A.OrderedHalves L) (N : Forest F L.ports.form) (start : A.Site→ℕ)
    (seedFloor : ∀ x,1+A.incidentWidth x ≤ start x) (seedWidth : ∀ x,L.ports.form.width x≤2*start x)
    (seed : ∀ x,(N x).resources ≤ start x) (c degree : ℕ) (scale : 2≤c*(16*u^10+1)^3)
    (prices : let R:=(B.repeat (u^8)).run rem A;R.FreshPath (c*(16*u^10+1)^3) h J (B.charges (u^8) rem A) start)
    (root : (((B.repeat (u^8)).run rem A).plan.finish h).Site) :
    let R:=(B.repeat (u^8)).run rem A
    let tree:=(R.plan.assemble h (R.wordAssembly J L) N).2 root
    10000*(tree.compile.cells+tree.compile.internal)≤B.archiveUnit u c degree*R.chargeAt h (B.charges (u^8) rem A) start root := by
  let R:=(B.repeat (u^8)).run rem A
  let C:=B.charges (u^8) rem A
  let K:=c*(16*u^10+1)^3
  let tree:=(R.plan.assemble h (R.wordAssembly J L) N).2 root
  have positiveRate : 0 < K := lt_of_lt_of_le (by decide : 0 < 2) scale
  have paid:=R.assembled_resources h J C ((B.repeat (u^8)).certified_floor _ (B.factor_bound _) rem A)
    L ord N start seedFloor seedWidth K scale prices
    (fun x => (seed x).trans (Nat.le_mul_of_pos_left (start x) positiveRate))
    _ ((B.repeat (u^8)).stageLength_run rem A) root
  change tree.resources≤B.terminalRowRate u c*R.chargeAt h C start root at paid
  have intrinsic : tree.compile.cells+tree.compile.internal≤tree.resources:=by
    have counted (rows bits nodes pins : ℕ) : rows + bits ≤ bits + rows + nodes + pins := by omega
    rw [tree.compiled_rows, tree.compiled_bits]
    exact counted tree.rows tree.bits tree.nodes tree.footprint.pins
  calc
    _ ≤ 10000*(B.terminalRowRate u c*R.chargeAt h C start root):=Nat.mul_le_mul_left _ (intrinsic.trans paid)
    _ = 10000*B.terminalRowRate u c*R.chargeAt h C start root:=by ring
    _ ≤ _:=Nat.mul_le_mul_right _ (B.weighted_rows_le_archiveUnit degree c)

end

end ThreeFlat.Diagonal.PhysicalStage.Block

namespace ThreeFlat.Diagonal.PhysicalStage.Block
open RAM.HistoryStageBody.Physical
noncomputable section
variable {F : Type} [Field F] [Fintype F] (B : Block F)

/-- The finite grid-page coefficient is included in the archive's existing age
threshold. The true site charge pays the LUT, compactor and scalar pages. -/
theorem grid_page_margin {u degree unitWork amount cap : ℕ} {g : Grid F} (placed : g∈grids B)
    (live : 1≤amount) (unit : B.archiveUnit u B.localCoefficient degree≤unitWork)
    (peak : unitWork*amount≤cap) :
    gridPageRate (arity B) g*((amount+1)*(16*u^10+1)^3)≤cap := by
  let levels:=(B.repeat (u^8)).length
  let cubes:=(16*u^10+1)^3
  let rate:=gridPageRate (arity B) g
  have rate_bound : rate≤B.stageClockRate := (grid_page_rate_le_block B placed).trans (Nat.le_add_left ..)
  have two : 2 ≤ 10 * (levels + 2)^2 := by
    have square_pos : 0 < (levels + 2)^2 := Nat.pow_pos (by omega)
    exact (by decide : 2 ≤ 10).trans (Nat.le_mul_of_pos_right 10 square_pos)
  have one : 1≤B.localCoefficient:=by unfold localCoefficient;omega
  have cubic : cubes≤B.localCoefficient*cubes:=by simpa using Nat.mul_le_mul_right cubes one
  have reserve : 2*rate*cubes≤unitWork := calc
    2*rate*cubes ≤ 10*(levels+2)^2*B.stageClockRate*(B.localCoefficient*cubes) :=
      Nat.mul_le_mul (Nat.mul_le_mul two rate_bound) cubic
    _ = B.stageUnit u B.localCoefficient:=rfl
    _ ≤ _ := (Nat.le_add_right ..).trans unit
  calc
    _ ≤ rate*((2*amount)*cubes) := Nat.mul_le_mul_left rate (Nat.mul_le_mul_right cubes (by omega))
    _ = (2*rate*cubes)*amount:=by ring
    _ ≤ unitWork*amount:=Nat.mul_le_mul_right _ reserve
    _ ≤ _:=peak

end

end ThreeFlat.Diagonal.PhysicalStage.Block

namespace ThreeFlat.Diagonal.PhysicalStage.Block
open RAM.HistoryStageBody.Physical
noncomputable section
variable {F : Type} [Field F] [Fintype F] (B : Block F)

/-- The age threshold for the single archive tariff covers every fixed grid
header and mask used to initialize the native party pages. -/
theorem blockPageRate_at_age {u : ℕ} (bound : B.archiveConstant B.localCoefficient≤u) : blockPageRate B≤u := by
  have scale : 1≤B.localCoefficient:=by unfold localCoefficient;omega
  have price : blockPageRate B≤B.stageClockRate:=Nat.le_add_left ..
  have first : B.stageClockRate≤40*B.stageClockRate:=by omega
  have weight : 40*B.stageClockRate≤40*B.stageClockRate*B.localCoefficient:=
    Nat.le_mul_of_pos_right _ scale
  exact price.trans (first.trans (weight.trans ((Nat.le_add_right ..).trans bound)))

end

end ThreeFlat.Diagonal.PhysicalStage.Block

end
end OAI
