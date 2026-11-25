import OAI.Computability.BorderVNP.DiagonalCalendarPacketNumerals
import OAI.Computability.BorderVNP.DiagonalFrozenExecutionRange
import OAI.Computability.BorderVNP.PackedFrozenBundleShape

/-! # Native scanner bounds for the original bundles of a signed calendar -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Cover Epoch Packing Packing.DeckGrid Packing.BottomReports
open PackedHistoryCircuit.Normalized SelectedSchedule EnrichedOuter TeamScales
open Branch ExternalSew

open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {paid : PaidIdentity F D m}
    {S : SiteSchedule paid} {cube : FixedCube K} {extra E p Q breadth sourcePower : ℕ}
    {scales : EpochScales S (cube.pred+1) extra}
    {b : JointSchedule.{0} scales (E+1) (max (5*(E+2)) p) Q 3076 (breadth+10) (sourcePower+1)}
    {φ : K →+* F} {q : ℕ} {hm : 0 < m} {header C A₀ a B₀ b₀ J j coeff addr power cut : ℕ}
    {adv : ℕ → ℕ} {c charge factor l : ℕ}
    (cal : SignedCalendarAt cube b φ q hm header C A₀ a B₀ b₀ J j coeff addr power cut adv c charge factor (l+1))
    (oper : FrozenExecutionAt cube b φ q adv c charge header (hm:=hm) (l+1)) (qpos : 1 ≤ Q)

local notation "r₁" => stretch b.ρ (l+1)
local notation "size₁" => stretch b.σ (l+1)
local notation "w₁" => b.physical.word (l+1)
local notation "short₁" => 60*logWidth r₁ (l+1)
local notation "T₁" => epochs scales.τ (l+1)
local notation "d₁" => CoverScale.initialDepth (Cube D) r₁ (l+1)-1
local notation "axes" => Fintype.card (Cube D)
local notation "copies₁" => TeamScales.width (l+1) scales.α
local notation "J₁" => (fan S)^T₁*GridHosts.tileCount axes d₁
local notation "desc₁" => seedDescriptionWidth (l+1) r₁ axes d₁ (header*logWidth r₁ (l+1))
  (BottomGridBank.bodyBudget (seedBoxCapacity (l+1) r₁ axes d₁ (Fintype.card (Direction axes))))

variable (position : (Fin (Fintype.card (Cube D)) → Deck (CoverScale.initialDepth (Cube D)
      (stretch b.ρ (l+1)) (l+1)-1+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)

attribute [local irreducible] Nat.clog TeamScales.logWidth Fintype.equivFin ChosenReader.charge stretch
  Branch.pairedTableParameters
set_option maxRecDepth 7000 in
set_option maxHeartbeats 3500000 in
/-- The scan of the original bundles fits the native word, from the sorted cell keys
through every selected copy count and original source interval. -/
theorem SignedCalendarAt.frozenOpeningBundleFit :
    let task := cal.frozenTask (ord:=ord) (common:=common) oper.grid qpos position chart reader chargeFit
    let shapes : Fin J₁ → BundleSort.Shape := cal.frozenWitness.frozenBundleShapes position ((fan S)^T₁) copies₁
    task.cube.cells < 2^short₁ ∧ desc₁ < 2^w₁ ∧ 2^Nat.clog 2 J₁*desc₁ < 2^w₁ ∧
      (∀ i, (shapes i).copies < 2^w₁) ∧
      ∀ i, bottomStride ((shapes i).fine+(shapes i).incoming) (shapes i).cap < 2^w₁ := by
  intro task shapes
  have packet := (cal.frozenPacketInputs oper.grid position oper.grid.sites_pos).2.1
  have fit := oper.bundleSortRoom w₁ packet.2.2.2.1 0 (Nat.zero_le _)
  have keys : task.cube.cells < 2^short₁ := by
    change CoverScale.sites (Cube D) (EnrichedOuter.depth S _ T₁) < _
    rw [←oper.grid.depth_eq]
    exact (Nat.le_succ _).trans_lt packet.2.2.2.2.1
  refine ⟨keys,fit.2.2.1,fit.2.2.2.1,fun _ => fit.1,?_⟩
  intro i
  let order := (Fintype.equivFin (Fin axes → Deck (d₁+2))).symm
  exact (cal.frozenWitness.seedBundleShape_stride position (order (finProdFinEquiv.symm i).2) copies₁).trans_lt fit.2.1

end Diagonal

end BorderVNP
end Computability
end OAI
