import OAI.Computability.BorderVNP.PackedHistoryRealizedSchedule
import OAI.Computability.BorderVNP.PackedHistorySeedWord
import OAI.Computability.BorderVNP.PackedHistoryNormalizedGrid

/-! # The complete geometric history on the actual repeated private grid -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover BorderVNP.Epoch Packing Shortening PublicCapacity Diagonal Diagonal.ExternalSew
open TeamScales Filter EnrichedOuter
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {D m : ℕ} [NeZero D] {K : Type u} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

local notation "axes" => Fintype.card (Cube D)
local notation "degree" => Fintype.card (DeckGrid.Direction axes)

/-- The realized geometry circuit uses the actual grouped seed port type,
real channel width and immutable tape length on the chosen bottom cover. -/
structure SeedPlan (n r d T copies headerFactor Q : ℕ) where
  /-- Every selected epoch is above the preparation cutoff. -/
  deep : S.floor+1+S.drop*T ≤ d+1
  /-- Concrete compiled sparse histories for the repeated physical grouped grid. -/
  compiled : Compiled (fun _ : Fin (GridHosts.tileCount axes d) => copies*GridHosts.inputBlockWidth r n axes d) deep
    (boundaryBudget S (initialMass (D:=D) n r d copies headerFactor))
    (innerCap S (initialMass (D:=D) n r d copies headerFactor)) (60*logWidth r n)
  /-- Exact initial grid identifiers fit in the common processor word. -/
  fits : GridHosts.tileCount axes d ≤ 2^(60*logWidth r n)
  /-- Every repeated channel width fits in that word. -/
  small : copies*DeckGrid.seedChannelWidth n r axes d < 2^(60*logWidth r n)
  /-- The complete concrete gate list and literal profile bits fit the execution budget. -/
  within : WithinHistoryBudget S (r:=r) (n:=n) _ deep (initialMass (D:=D) n r d copies headerFactor) Q compiled

/-- All geometry programs and their word fits are realized on the true bottom
grid at the selected cover depth. The global seed budget follows from the
publicly padded one-copy tape and physical channel lengths on that grid. -/
theorem eventually_measured_seed (hm : 0 < m) {a x : ℕ} (scales : EpochScales S a x)
    (physical : ∀ d ≥ S.floor, S.FitsLevels d ∧ S.HasLeaves d ∧ S.RunsEnriched.{max 1 u,u} d)
    (headerFactor Q : ℕ) :
    ∃ A a₀ B b J j : ℕ, ∃ ω : ℝ, 0<ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → (r:ℝ)≤2^((n:ℝ)^ω) →
      ∃ plan : SeedPlan S n r (CoverScale.initialDepth (Cube D) r n-1) (epochs scales.τ n)
        (TeamScales.width n scales.α) headerFactor Q,
          Machine.LocalSizes (r:=r) (n:=n) A a₀ B b J j plan.compiled.machine := by
  obtain ⟨A,a₀,B,b,J,j,u,hu,realized⟩ := eventually_realized_sizes S hm scales physical Q
  obtain ⟨v,hv,words⟩ := eventually_initial_words S scales headerFactor
  refine ⟨A,a₀,B,b,J,j,min u v,lt_min hu hv,?_⟩
  filter_upwards [realized,words,eventually_ge_atTop 1] with n haveR fit hn
  intro r hr room
  let start := CoverScale.initialDepth (Cube D) r n
  let d := start-1
  let T := epochs scales.τ n
  let copies := TeamScales.width n scales.α
  let base := initialMass (D:=D) n r d copies headerFactor
  have depth_eq : d+1=start := by
    have hs : 1 ≤ start := Nat.succ_pos _
    dsimp only [d]; omega
  have stretch (i : ℝ) (hi : min u v ≤ i) : (r:ℝ)≤2^((n:ℝ)^i) :=
    room.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : 1≤(n:ℝ)) hi))
  obtain ⟨hbase,tiles,edges⟩ := fit r hr (stretch v (min_le_right ..))
  let bits := fun _ : Fin (GridHosts.tileCount axes d) => copies*GridHosts.inputBlockWidth r n axes d
  obtain ⟨deep,R,localSize,budget⟩ := haveR r hr (stretch u (min_le_left ..)) base hbase _ bits
  have machine : ∃ h : S.floor+1+S.drop*T ≤ d+1,
      ∃ C : Compiled bits h (boundaryBudget S base) (innerCap S base) (60*logWidth r n),
        Machine.LocalSizes (r:=r) (n:=n) A a₀ B b J j C.machine ∧ WithinHistoryBudget S (r:=r) (n:=n) bits h base Q C := by
    rw [depth_eq]
    exact ⟨deep,R,localSize,budget⟩
  obtain ⟨h,C,localC,hC⟩ := machine
  exact ⟨⟨h,C,tiles,edges,hC⟩,localC⟩

/-- All geometry programs and their word fits are realized on the true bottom
grid at the selected cover depth. The global seed budget follows from the
publicly padded one-copy tape and physical channel lengths on that grid. -/
theorem eventually_seed_plan (hm : 0 < m) {a x : ℕ} (scales : EpochScales S a x)
    (physical : ∀ d ≥ S.floor, S.FitsLevels d ∧ S.HasLeaves d ∧ S.RunsEnriched.{max 1 u,u} d)
    (headerFactor Q : ℕ) :
    ∃ ω : ℝ, 0<ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → (r:ℝ)≤2^((n:ℝ)^ω) →
      Nonempty (SeedPlan S n r (CoverScale.initialDepth (Cube D) r n-1) (epochs scales.τ n)
        (TeamScales.width n scales.α) headerFactor Q) := by
  obtain ⟨A,a₀,B,b,J,j,ω,hω,run⟩ := eventually_measured_seed S hm scales physical headerFactor Q
  refine ⟨ω,hω,?_⟩
  filter_upwards [run] with n h
  intro r hr room
  obtain ⟨plan,_⟩ := h r hr room
  exact ⟨plan⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
