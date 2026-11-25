import OAI.Computability.BorderVNP.DiagonalCalendarTaskRoom
import OAI.Computability.BorderVNP.DiagonalPrefixFinishCalibration
import OAI.Computability.BorderVNP.PackedNativeReportMarkBounds
import OAI.Computability.BorderVNP.PackedRetainedReportUse
import OAI.Computability.BorderVNP.PackedSeedLiteralMatrix

/-! # Original marked report operands on the selected calendar's word size -/

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
local notation "size₁" => stretch b.σ (l+1)
local notation "R₁" => b.physical.teamsPred (l+1)
local notation "w₁" => b.physical.word (l+1)
local notation "ξ₁" => (scales.τ:ℝ)/5
local notation "ℓ₁" => TeamScales.link (ξ₁) (R₁+1) (l+1)
local notation "ec₁" => Wires.sortExponent (block (ξ₁) (l+1))
local notation "budget₁" => adv (adviceScale b.σ b.ρ (l+1))
local notation "pins₁" => (pairedTableParameters (l+1) (size₁)+2)*(budget₁+6)
local notation "d₁" => CoverScale.initialDepth (Cube D) (r₁) (l+1)-1
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes (d₁)
local notation3 (prettyPrint := false) "geo₁" => cal.sites.choose
local notation3 (prettyPrint := false) "prog₁" => cube.signedSiteProgram paid
local notation "a₁" => FieldProcessor.freeWidth (prog₁) scales.α 32 64 (r₁) (w₁) (l+1)
local notation "extra₁" => setupWidth (w₁+1) (l+1)+(prefixCapacity (r₁) 32 64 (w₁) (l+1)+1+a₁)
local notation3 (prettyPrint := false) "tape₁" => tapeTemplate (R:=R₁) (r:=r₁) (link:=ℓ₁) (regs:=64) (w:=w₁)
  (e:=ec₁) (width:=w₁+1) (k:=l) (a:=extra₁) (prog₁) (geo₁).fits (pins₁)

variable (grid : LocatedSignedGridAt cube b header (l+1)) (qpos : 1 ≤ Q)
    (position : (Fin (Fintype.card (Cube D)) → Deck (CoverScale.initialDepth (Cube D)
      (stretch b.ρ (l+1)) (l+1)-1+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
local notation "T₁" => epochs scales.τ (l+1)
local notation "copies₁" => TeamScales.width (l+1) scales.α

variable {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)

open Packing.BottomReports DiagonalTallyCellReports

local notation3 (prettyPrint := false) "trueTask" => cal.frozenTask grid qpos position chart reader chargeFit

include grid qpos chart reader chargeFit in
/-- Every parameter and every shift in the original source bundles is
addressable on the selected physical machine. This holds on arbitrary
retained banks, including the report rows of an unsuccessful proposal. -/
theorem SignedCalendarAt.frozenSourceCells_marks
    {bundles sites edges ports chans bins cells : ℕ}
    (original : Fin bundles ≃ Fin ((fan S)^T₁) × (Fin axes → Deck (d₁+2)))
    (siteID : (cal.frozenWitness.routedFine position).Site ↪ Fin sites)
    (edgeID : (cal.frozenWitness.routedFine position).Edge ↪ Fin edges)
    (portID : Fin r₁ × Fin (publicWidth tape₁) ↪ Fin ports)
    (channels : ((Fin axes → Deck (d₁+2)) × Direction axes) ↪ Fin chans)
    (groups : Fin tiles ↪ Fin bins) (slot base : Fin bundles → ℕ) (bank : Fin bundles → ℕ → Bool)
    (L : ReportLayout) (home : Fin bundles → Fin cells) (team : ℕ)
    (owner external supply privateWidth : ℕ → ℕ) (digits : ℕ → Fin L.gadgets → Fin L.countWidth → Bool) :
    let payload := cal.frozenWitness.retainedBundle (copies:=copies₁) position original
      (ParseTable.signedLiteralCode (s:=size₁) ord) siteID edgeID portID channels groups slot base bank
    ∀ row∈ReportDirectory.sourceCells L home payload team owner external supply privateWidth digits,
      ∀ bundle∈row.bundles, ∀ mark∈bundle.positions, mark.parameter<2^w₁ ∧ mark.place<w₁ := by
  intro payload
  apply ReportDirectory.sourceCells_marks
  have high := (cal.frozenTask_room grid qpos position chart reader chargeFit).2.1
  have dim := ((trueTask).finish_word_room high).2.1
  have labels : Branch.pairedTableParameters (l+1) size₁ ≤ 2^w₁ := (Nat.le_add_right ..).trans dim.le
  have width : logWidth r₁ (l+1) ≤ w₁ := Nat.le_self_pow (by omega : E+2≠0) _
  intro j
  exact cal.frozenWitness.seedReport_marks position (ParseTable.signedLiteralCode (s:=size₁) ord)
    siteID edgeID portID (original j).2 (stretch_one b.ρ (l+1)) width
    (fun s => (ParseTable.numberedLabelEquiv ord l size₁ s).isLt.trans_le labels)

end Diagonal

end BorderVNP
end Computability
end OAI
