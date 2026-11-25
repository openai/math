import OAI.Computability.BorderVNP.DiagonalFrozenIntervalBudget

/-! # Admissible private report funding before selection of an execution -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Crossing Cover BorderVNP.Epoch Packing Packing.DeckGrid Packing.Inherited Packing.PhysicalEpochs TeamScales
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open ExternalSew EnrichedOuter RoutingISA RoutingISA.SignedTaskArena TeamContraction.ProcessorSlots
open scoped Classical BigOperators BorderVNP.Epoch.Cube

set_option maxHeartbeats 1100000
set_option maxRecDepth 5500

variable {F K : Type} [Field F] [Field K] {D m : ℕ} [NeZero D] {e : PaidIdentity F D m}
    {S : SiteSchedule e} (cube : FixedCube K)
    {extra E dlog Q A B j : ℕ} {s : EpochScales S (cube.pred+1) extra}


/-- Simultaneous funding for each frozen task and each original sewn grid at length `n`. -/
def FrozenPrivateFundingAt (b : JointSchedule.{0} s (E+1) dlog Q A B j) (header n : ℕ) : Prop :=
  let r := stretch b.ρ n
  let d := CoverScale.initialDepth (Cube D) r n-1
  let T := epochs s.τ n
  let copies := TeamScales.width n s.α
  let w := b.physical.word n
  let link := b.physical.link n
  (∀ work (plan : SeedPlan S n r d T copies header work)
    (count : (fan S)^T*copies=b.physical.teamsPred n+1), plan.SewnCellLoads count link) ∧
    ∀ l size (initial : StartupArena) (dir : Packing.Directory.Layout)
      (profile ceiling outputs field : ℕ) (dirs : GeometryDirectories),
      let task := b.frozenSignedTask cube n l size header initial dir profile ceiling outputs field dirs
      FrozenIntervalBudget S n r d T copies header link w (E+2) task.p ∧
        (∀ z : e.Entry, cube.scalarNumber e (.inl z) ≤ task.p.report.gadgets-1) ∧
        (∀ z : BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width,
          cube.cubeID e z ≤ task.p.report.gadgets-1)

/-- The private report budget holds uniformly before choosing the original grid, reader or pin. -/
theorem JointSchedule.eventually_frozen_private_funding (b : JointSchedule.{0} s (E+1) dlog Q A B j)
    (header : ℕ) (large : E+2 ≤ dlog) : ∀ᶠ n : ℕ in atTop, FrozenPrivateFundingAt cube b header n :=
  b.eventually_frozen_interval_budget cube header large

end Diagonal

end BorderVNP
end Computability
end OAI
