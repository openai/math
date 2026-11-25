import OAI.Computability.BorderVNP.DiagonalCalendarControlFormats
import OAI.Computability.BorderVNP.DiagonalCalendarControlDirectories
import OAI.Computability.BorderVNP.DiagonalSignedControlWordRoom

/-! # All published scalar controls fit the physical signed word -/

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

/-- Each natural number offered to the control-word encoder is in range
before reduction modulo the physical word size. This holds on the located
calendar without choosing an exterior history or report assignment. -/
theorem SignedCalendarAt.frozenTask_controlWords (i : Fin 37) :
    (cal.frozenTask grid qpos position chart reader chargeFit).controls i.val < 2^w₁ := by
  let task := cal.frozenTask grid qpos position chart reader chargeFit
  have cutoff := (cal.frozenTask_room grid qpos position chart reader chargeFit).2.1
  obtain ⟨cells,reportCells,headerFit,gap,site,body,count⟩ :=
    cal.frozenControlFormats grid qpos position chart reader chargeFit
  obtain ⟨sorted,padded,stops,payload,inverse⟩ := cal.frozenControlDirectories grid qpos position chart reader chargeFit
  exact task.controls_word_of_scalars cutoff cells reportCells count.le (sorted.trans_lt headerFit)
    (padded.trans_lt headerFit) (stops.trans_lt headerFit) (payload.trans_lt headerFit)
    (inverse.trans_lt headerFit) gap site body i

/-- Reading the encoded field yields the natural control of the installed task. -/
theorem SignedCalendarAt.frozenTask_controlWord_value (i : Fin 37) :
    let task := cal.frozenTask grid qpos position chart reader chargeFit
    (Fin.ofNat (2^w₁) (task.controls i.val)).val = task.controls i.val :=
  Nat.mod_eq_of_lt (cal.frozenTask_controlWords grid qpos position chart reader chargeFit i)

end Diagonal

end BorderVNP
end Computability
end OAI
