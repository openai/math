import OAI.Computability.BorderVNP.DiagonalCalendarTaskRoom
import OAI.Computability.BorderVNP.DiagonalPrefixFinishCalibration

/-! # Scalar widths of the installed signed control table -/

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
set_option maxHeartbeats 1900000

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {paid : PaidIdentity F D m}
    {S : SiteSchedule paid} {cube : FixedCube K} {extra E p Q breadth sourcePower : ℕ}
    {scales : EpochScales S (cube.pred+1) extra}
    {b : JointSchedule.{0} scales (E+1) (max (5*(E+2)) p) Q 3076 (breadth+10) (sourcePower+1)}
    {φ : K →+* F} {q : ℕ} {hm : 0 < «m»} {header C A₀ a B₀ b₀ J j coeff addr power cut : ℕ}
    {adv : ℕ → ℕ} {c charge factor l : ℕ}
    (cal : SignedCalendarAt cube b φ q hm header C A₀ a B₀ b₀ J j coeff addr power cut adv c charge factor (l+1))

local notation "r₁" => stretch b.ρ (l+1)
local notation "w₁" => b.physical.word (l+1)

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

/-- The real allocated cell and report rows are nonempty, and the external
description scalars of the installed 37-word control fit the native word.
The quadratic reserved gap is bounded by a single genuine cell stride;
the site field and opaque body are bounded by their literal description. -/
theorem SignedCalendarAt.frozenControlFormats :
    let task := cal.frozenTask grid qpos position chart reader chargeFit
    0 < task.cube.cells ∧ 0 < task.p.report.cells ∧ task.cube.header.header < 2^w₁ ∧
      task.p.privateGap < 2^w₁ ∧ task.p.siteWidth < 2^w₁ ∧ task.p.bodyCap < 2^w₁ ∧
      task.p.report.countWidth = w₁ := by
  intro task
  have cells : 0 < task.cube.cells := by
    change 0 < Fintype.card ((Cube D) → Deck _)
    exact Fintype.card_pos
  have endFit := (cal.frozenTask_room grid qpos position chart reader chargeFit).2.1
  have before : task.before.limit < 2^w₁ := (task.finish_word_room endFit).2.2.2
  have full : task.cube.stop ≤ task.before.limit := by
    apply le_trans _ (show task.before.start ≤ task.before.limit by rw [task.before.footprint]; omega)
    apply le_trans _ task.constants_le_before
    unfold CubeConstants.arenaEnd CubeConstants.idBase
    omega
  have stop := full.trans_lt before
  have headerFit : task.cube.header.header < 2^w₁ :=
    (task.open_table_order.1.trans (Nat.le_add_right ..)).trans_lt stop
  have stride : task.cube.cellStride ≤ task.cube.stop := by
    unfold CubeArena.Layout.stop
    exact (Nat.le_mul_of_pos_left _ cells).trans (Nat.le_add_left ..)
  have gap : (l+1)^2 ≤ task.cube.cellStride := by
    change (l+1)^2 ≤ 3*(r₁*(l+1))^2+1
    have expanded := Nat.pow_le_pow_left (Nat.le_mul_of_pos_left (l+1) (stretch_one b.ρ (l+1))) 2
    omega
  have gapFits := (gap.trans stride).trans_lt stop
  have low : l+1 < 2^w₁ := (Nat.le_self_pow (by decide : 2 ≠ 0) _).trans_lt gapFits
  have sizes : task.p.siteWidth+task.p.bodyCap ≤ l+1 := by
    apply le_trans _ grid.literalRanges.2.2.1
    change _ ≤ (_+_)+_
    exact Nat.le_add_right ..
  exact ⟨cells,cells,headerFit,gapFits,by omega,by omega,rfl⟩

end Diagonal

end BorderVNP
end Computability
end OAI
