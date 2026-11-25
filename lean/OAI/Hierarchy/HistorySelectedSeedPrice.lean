import OAI.Hierarchy.HistorySelectedArchitecture
import OAI.Hierarchy.HistorySelectedSeedRun
import OAI.ThreeFlat.Diagonal.PhysicalVisitRates

namespace OAI
/-! # Charging the actual receiver seed instructions to the archive tariff -/

namespace Hierarchy.HistorySelectedSeed
open ThreeFlat RAM RAM.DescriptorExpr RAM.HistoryInitialSeed
open RAM.HistoryStageBody.Physical Computability.VPVNP.BurstRAM
open private leaf_price_bound leafRuntimeRate_eq from OAI.ThreeFlat.RAM.HistoryStageTariff
variable {F : Type} [Field F] [Fintype F] {W : ℕ}

theorem actual_ticks (A : Layout) (z : Site) (rom : TraceRawLookup.Layout)
    (amount : ℕ) (positive : 1≤amount) (rows : z.rows A≤amount)
    (pins : z.extPins≤2*amount) :
    ticks A z (TraceRawLookup.virtual W rom (TraceBucketAtom.publicProgram W))
      ≤leafRuntimeRate*amount := by
  let dec := TraceRawLookup.virtual W rom (TraceBucketAtom.publicProgram W)
  exact leaf_price_bound (4+42*(2*(HistoryInitialSeed.formula A).work+4)) (z.rows A) z.extPins
    (words A (liftDecoder dec)).binds amount (HistorySelectedOps.tariff []+3*rawLeafBinds) leafRuntimeRate
    (HistoryInitialSeed.seed_budget A) positive rows pins (virtual_words_price (W:=W) A rom) leafRuntimeRate_eq

theorem block_ticks (B : Diagonal.PhysicalStage.Block F) (A : Layout) (z : Site)
    (rom : TraceRawLookup.Layout) (amount : ℕ) (positive : 1≤amount)
    (rows : z.rows A≤amount) (pins : z.extPins≤2*amount) :
    ticks A z (TraceRawLookup.virtual W rom (TraceBucketAtom.publicProgram W))≤
      B.stageClockRate*amount := by
  apply (actual_ticks A z rom amount positive rows pins).trans
  apply Nat.mul_le_mul_right
  unfold Diagonal.PhysicalStage.Block.stageClockRate
  omega

end Hierarchy.HistorySelectedSeed

end OAI
