import OAI.Computability.BorderVNP.DiagonalCalendarArgumentRoom
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedReportGeometry
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerTask
import OAI.Computability.BorderVNP.DiagonalFrozenExecutionRange

/-! # Word widths of the host on the selected frozen calendar -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CellAddressCircuit.Fields

variable {s e p cells depth k w : ℕ} {σ : Type*}

/-- The bit width of an owner in this physical field. -/
abbrev ownerWidth (_ : Fields s e p cells depth k w σ) : ℕ := k

/-- The bit width of a cable, auxiliary, or port width in this physical field. -/
abbrev fieldWord (_ : Fields s e p cells depth k w σ) : ℕ := w

end Packing.CellAddressCircuit.Fields

namespace Diagonal

open Diagonal.ExternalSew Cover Packing Packing.DeckGrid Crossing Branch Epoch PackedHistoryCircuit
open PackedHistoryCircuit.Normalized SelectedSchedule TeamScales TeamContraction ProcessorSlots
open VPVNP FieldProcessor RoutingISA GeometryAdvice GeometryFrameEncoding
open DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins
open scoped Classical BorderVNP.Epoch.Cube

set_option maxRecDepth 8200
set_option maxHeartbeats 4000000

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {paid : PaidIdentity F D m}
    {S : SiteSchedule paid} {cube : FixedCube K} {extra E p Q breadth sourcePower : ℕ}
    {scales : EpochScales S (cube.pred+1) extra}
    {b : JointSchedule.{0} scales (E+1) (max (5*(E+2)) p) Q 3076 (breadth+10) (sourcePower+1)}
    {φ : K →+* F} {q : ℕ} {hm : 0 < «m»} {header C A₀ a B₀ b₀ J j coeff addr power cut : ℕ}
    {adv : ℕ → ℕ} {c charge factor l : ℕ}
    (cal : SignedCalendarAt cube b φ q hm header C A₀ a B₀ b₀ J j coeff addr power cut adv c charge factor (l+1))
    (oper : FrozenExecutionAt cube b φ q adv c charge header (hm:=hm) (l+1)) (qpos : 1 ≤ Q)
    (position : (Fin (Fintype.card (Cube D)) → Deck (CoverScale.initialDepth (Cube D)
      (stretch b.ρ (l+1)) (l+1)-1+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)

/-- The issued geometry's owner and field words fit the native machine. The
original directory and planner arena use the same word for every host index. -/
theorem SignedCalendarAt.frozenLookupHostWordBounds (values : _) (hist : _) :
    let field := (cal.frozenReportGeometry oper.grid qpos position chart reader chargeFit values hist).1
    let w := b.physical.word (l+1)
    let dir := cal.frozenDirectory
    let arena := (cal.frozenPlannerTask oper.grid qpos position chart reader chargeFit).cube
    field.ownerWidth ≤ field.fieldWord ∧ field.fieldWord ≤ w ∧ b.physical.teamsPred (l+1)+1 ≤ 2^w ∧
      stretch b.ρ (l+1) ≤ 2^w ∧ dir.fields ≤ 2^w ∧ dir.literal < 2^w ∧
      arena.cells ≤ 2^w ∧ arena.cellStride ≤ 2^w := by
  intro field w dir arena
  have short := (cal.frozenPacketInputs oper.grid position oper.grid.sites_pos).2.1.2.2.2.1
  have room := cal.frozenArgumentPublicationRoom oper.grid qpos position chart reader chargeFit oper.routing
  have layout := (cal.frozenEarlyTask oper.grid qpos position chart reader chargeFit).symm.trans
    (cal.frozenPlannerTask_eq oper.grid qpos position chart reader chargeFit)
  obtain ⟨_, _, teams, processors, fields, literal, cells, stride, _, _⟩ := room
  exact ⟨short, le_rfl, teams, processors, fields, literal,
    (congrArg (fun t : SignedTaskArena.Layout => t.cube.cells) layout) ▸ cells,
    (congrArg (fun t : SignedTaskArena.Layout => t.cube.cellStride) layout) ▸ stride⟩

end Diagonal

end BorderVNP
end Computability
end OAI
