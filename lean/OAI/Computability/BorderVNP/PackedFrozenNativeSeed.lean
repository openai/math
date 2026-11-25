import OAI.Computability.BorderVNP.PackedFrozenNativeSeedInterface
import OAI.Computability.BorderVNP.PackedFrozenNativeBudget

/-! # The actual grouped verifier grid and its complete chronological history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.Inherited.WorkWords Packing.Inherited.FrozenTape
open Diagonal Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction ParseBatch ParseBatchVerifier Prewire
open TeamScales Filter EnrichedOuter VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1900000
set_option maxRecDepth 6000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
local notation "axes" => Fintype.card (Cube D)

/-- One calibrated seed processor performs the full sparse immutable-record
computation, the two work scans, geometry, and all guesses within the strict
public exponent. Its cutoffs precede the arity, wiring and private witnesses. -/
theorem eventually_native_seed (hm : 0 < m) {a x : ℕ} (scales : EpochScales S a x)
    (physical : ∀ d ≥ S.floor, S.FitsLevels d ∧ S.HasLeaves d ∧ S.RunsEnriched.{1,0} d)
    (headerFactor Q : ℕ) :
    ∃ A a₀ B b J j : ℕ, ∃ ω : ℝ, 0<ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → (r:ℝ)≤2^((n:ℝ)^ω) →
      let d := CoverScale.initialDepth (Cube D) r n-1
      let T := epochs scales.τ n
      let copies := TeamScales.width n scales.α
      ∃ plan : SeedPlan S n r d T copies headerFactor Q, ∃ wr : WidthRanges S (d+1) T (60*logWidth r n),
        Machine.LocalSizes (r:=r) (n:=n) A a₀ B b J j plan.compiled.machine ∧ plan.TapeWithin S wr hm := by
  obtain ⟨A,a₀,B,b,J,j,u,hu,plans⟩ := eventually_measured_seed S hm scales physical headerFactor Q
  obtain ⟨v,hv,work⟩ := Compiled.eventually_native_budget S hm scales A a₀ B b J j 2 (5+64000*66^3) 3 Q
  refine ⟨A,a₀,B,b,J,j,min u v,lt_min hu hv,?_⟩
  filter_upwards [plans,work,eventually_native_bottom_range S scales,eventually_ranges S scales (fun _ => 0) (fun _ => 0),
    eventually_ge_atTop 1] with n chosen all rows range hn
  intro r hr room d T copies
  let start := CoverScale.initialDepth (Cube D) r n
  let L := logWidth r n
  have depth : d+1=start := by
    have pos : 1 ≤ start := Nat.succ_pos _
    change start-1+1=start
    omega
  have stretch (z : ℝ) (le : min u v ≤ z) : (r:ℝ)≤2^((n:ℝ)^z) := room.trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) le))
  obtain ⟨plan,sizes⟩ := chosen r hr (stretch u (min_le_left ..))
  have wr : WidthRanges S (d+1) T (60*L) := by rw [depth]; exact WidthRanges.of_ranges S (range r hr).2
  refine ⟨plan,wr,sizes,?_⟩
  intro teams time pins link inner Edge G order position σ fs f small fmt source
  have init := rows r hr
  dsimp only at init
  rw [←show d+1 = CoverScale.initialDepth (Cube D) r n from depth] at init
  have bound := all r hr (stretch v (min_le_right ..))
  dsimp only at bound
  rw [←show d+1 = CoverScale.initialDepth (Cube D) r n from depth] at bound
  exact bound plan.deep plan.compiled sizes fmt (Boundary.seedFormat_rows G order position copies) _ _ wr source
    (Boundary.seedTapeFrame_rowWork S plan G order position f small init.2 init.1)

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
