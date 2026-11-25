import OAI.Hierarchy.TraceRegisteredPinFloor
import OAI.Hierarchy.TraceNativeAdmittedWork

namespace OAI
/-! # The actual receiver's terminal pin allocation

The physical archive tariff is at least two. Its published peak therefore
covers the selected site's compiled pin table as well as its replay work.
-/

noncomputable section
namespace Hierarchy.TraceDistribution.Physical
open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open Filter Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Topology

variable {F : Type} [Field F] [Fintype F] (B : Block F)

/-- The scheduled word, its replay work, and all physical pins simultaneously
fit the selected terminal budget under the native trace parameter bounds. -/
theorem native_scheduled_pin_work_bounds {u s : ℕ → ℕ} (scale : Scale u s) (degree stageRate rootRate : ℕ) :
    ∃ C : ℕ,
    ∀ᶠ w : ℕ in atTop, ∀ {k low pc regs words S base fuel : ℕ}
      (M : Machine (64*w) pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
      (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (hk : 2≤k+1)
      (rem : ℕ) (e : k+1=(B.repeat (s w)).charge+rem) (_small : low≤w/2)
      (_q : Fintype.card F≤64*w) (_p : pc≤64*w) (_r : regs≤64*w) (_a : words≤64*w) (_d : (k+1)+low≤64*w),
      k+1≤2*(w+1) → (k+1)+low≤u w+1 → s w≤w →
      let d := (k+1)+low
      let grid := TraceStaticRow.gateTable hF t.width t.labels base fuel st regs words d
      let X := B.cursorState hk low (1+(d+d)) grid.cells
      let R := Program.recast e X ((B.repeat (s w)).run rem (e ▸ X))
      let reg := registerOnLanes B (Fin S → Bool) (s w) rem X e
      let L := TraceReceiverSeedWords.wordsLayout M t hF st B hk
      let N := TraceReceiverSeedWords.forest M t hF st B hk
      let start := TraceReceiverSeedWords.start M t hF st B hk
      let stageCount := (B.repeat (s w)).length
      ∀ h : R.plan.History,
        let depth:=4+stageCount
        let setup:=TraceFactorReceiver.Gather.setupPrice stageCount stageRate
        let maps:=TraceFactorReceiver.Gather.mapPrice degree rootRate
        let unit := FactorWork.archiveTariff w depth setup maps stageCount B.localCoefficient
        let W := publishedWork R h reg.2 start unit
        (∑ v,W v) ≤ 2^(u w)*C*(w+1)^51 ∧
          ∀ v, FactorWork.work R.plan h (R.wordAssembly reg.1.steps L) N depth setup maps v ≤ W v ∧
            W v ≤ 2^(3*w/5) ∧
            (R.plan.assemble h (R.wordAssembly reg.1.steps L) N).1.width v ≤ 2^(3*w/5) := by
  obtain ⟨C, fits⟩ := native_scheduled_work_bounds B scale degree stageRate rootRate
  refine ⟨C, ?_⟩
  filter_upwards [fits] with w bound
  intro k low pc regs words S base fuel M t hF st hk rem e small q hp hr ext dFits axes round blocks
    d grid X R reg L N start stageCount h depth setup maps unit W
  have both := bound M t hF st hk rem e small q hp hr ext dFits axes round blocks h
  refine ⟨both.1, fun v => ⟨(both.2 v).1, (both.2 v).2, ?_⟩⟩
  exact native_factor_pins B M t hF st hk (s w) rem e h depth setup maps (3*w/5) v (both.2 v).2


end Hierarchy.TraceDistribution.Physical

end
end OAI
