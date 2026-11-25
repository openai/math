import OAI.Computability.BorderVNP.PackedSelectedScheduleRanges
import OAI.Computability.BorderVNP.PackedHistoryNormalizedOuter

/-! # The level of each selected public node in its enclosing enriched epoch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover Epoch Shortening PublicCapacity Packing Diagonal Filter TeamScales
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- The scheduled kernel operates at the same depth as its physical
enriched program, at every inner stage including the terminal boundary. -/
theorem level_offset {start T t : ℕ} (deep : S.floor+1+S.drop*T ≤ start) (ht : t<T) (j : ℕ) :
    S.level (EnrichedOuter.offset S start t) j = stageLevel S start t j := by
  let word := fun i => (S.source.pattern i).word
  change Adaptive.Levels.level word (S.high (EnrichedOuter.offset S start t)-S.drop) S.last j =
    Adaptive.Levels.level word (start-S.drop*(t+1)) S.last j
  rw [SiteSchedule.high,Nat.add_sub_cancel]
  exact congrArg (fun d => Adaptive.Levels.level word d S.last j) (EnrichedOuter.levels S deep ht).2.1

/-- The actual rounded initial depth permits all outer enriched epochs and
bounds the bottom grid volume uniformly in r. -/
theorem eventually_offsets {a x : ℕ} (s : EpochScales S a x) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r →
      let start := CoverScale.initialDepth (Cube D) r n
      S.floor+1+S.drop*epochs s.τ n ≤ start ∧
        (CoverScale.sites (Cube D) start:ℝ) ≤ r*(n:ℝ)^(9/10:ℝ) := by
  have τ : 0 ≤ (s.τ:ℝ) := by exact_mod_cast s.tau_pos.le
  have cov := s.rate (epochCoverLoss_pos S) (epochGrowth_bounds S x).2.2.1
  have rate : (s.τ:ℝ)*Real.logb 2 ((CoverScale.factor (Cube D):ℝ)^S.drop) ≤ (s.α:ℝ)/10 := by
    simpa only [epochCoverLoss,Nat.cast_pow] using cov
  filter_upwards [CoverScale.eventually_depths (Cube D) S.drop S.floor τ rate (by linarith [s.alpha_small])]
    with n room
  intro r hr start
  obtain ⟨floor,eq,_,vol,_⟩ := room r hr
  exact ⟨(Nat.add_le_add_right floor _).trans_eq eq,vol⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
