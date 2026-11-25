import OAI.Computability.BorderVNP.DiagonalCalendarFeasiblePost

/-! # Finish windows at the dimensions read by the physical writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Diagonal.ExternalSew Cover Packing Packing.DeckGrid Crossing Branch Epoch PackedHistoryCircuit
open PackedHistoryCircuit.Normalized SelectedSchedule EnrichedOuter TeamScales TeamContraction ProcessorSlots
open VPVNP ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open FieldProcessor RoutingISA RoutingISA.Evaluator RoutingISA.Transmission
open GeometryAdvice GeometryFrameEncoding RoutingISA.Pins VPVNP.BurstRAM RoutingISA.CompactMachine TeamSite
open DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins
open scoped Classical BorderVNP.Epoch.Cube

set_option maxRecDepth 7000
set_option maxHeartbeats 4300000

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {paid : PaidIdentity F D m}
    {S : SiteSchedule paid} {cube : FixedCube K} {extra E p Q breadth sourcePower : ℕ}
    {scales : EpochScales S (cube.pred+1) extra}
    {b : JointSchedule.{0} scales (E+1) (max (5*(E+2)) p) Q 3076 (breadth+10) (sourcePower+1)}
    {φ : K →+* F} {q : ℕ} {hm : 0 < «m»} {header C A₀ a B₀ b₀ J j coeff addr power cut : ℕ}
    {adv : ℕ → ℕ} {c charge factor l : ℕ}
    (cal : SignedCalendarAt cube b φ q hm header C A₀ a B₀ b₀ J j coeff addr power cut adv c charge factor (l+1))

local notation "r₁" => stretch b.ρ (l+1)
local notation "w₁" => b.physical.word (l+1)
local notation "R₁" => b.physical.teamsPred (l+1)
local notation "ξ₁" => (scales.τ : ℝ)/5

variable (grid : LocatedSignedGridAt cube b header (l+1)) (qpos : 1 ≤ Q)
    (position : (Fin (Fintype.card (Cube D)) → Deck (CoverScale.initialDepth (Cube D)
      (stretch b.ρ (l+1)) (l+1)-1+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
variable {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)


open RoutingISA.Evaluator.ScheduleClock

/-- The native writer uses the deployed sort depths and power digits, with
its public and local work computed from the cube stored in the task. -/
theorem SignedCalendarAt.frozenWriterFinishWindows
    (rate : CalendarPostRateAt cube b φ q adv c charge (l+1)) :
    let task := cal.frozenTask grid qpos position chart reader chargeFit
    let dims := cal.frozenPacketSortShape grid position
    task.FinishWindows r₁ w₁ dims.1 dims.2.1 (Nat.clog 2 (r₁*(2*l+1)+1)) (exterior ξ₁ r₁ (l+1))
      ⌈publicWork (task.cube.n+1) scales.α r₁ (l+1) (R₁+1)⌉₊
      ⌈localWork (task.cube.n+1) (E+2) scales.α ξ₁ r₁ (l+1) (R₁+1)⌉₊ reader.charge := by
  intro task dims
  have axis : task.cube.n = cube.pred := rfl
  rw [axis]
  exact (cal.frozenDeployedFeasiblePost grid qpos position chart reader chargeFit rate).windows

end Diagonal

end BorderVNP
end Computability
end OAI
