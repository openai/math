import OAI.Computability.BorderVNP.PackedSelectedRecordRanges
import OAI.Computability.BorderVNP.PackedSeedSewnCaps

/-! # The true repeated seed payload supplies the calibrated selector word

The seed uses the actual finite-cover channel width, grouped verifier input
and padded private descriptor. Its expanded-record allowance propagates
through each physical named combining stage at the processor word scale.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover Epoch Shortening Packing Diagonal TeamScales Filter
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

omit [NeZero D] in
/-- The coordinate enumeration used by the seed's wired grid chooses exactly the
same rounded starting level as the physical cube-valued program. -/
theorem initialDepth_fin (n r : ℕ) :
    CoverScale.initialDepth (Fin (Fintype.card (Cube D))) r n = CoverScale.initialDepth (Cube D) r n := by
  simp only [CoverScale.initialDepth,CoverScale.sites,CoverScale.factor,Fintype.card_fun,Fintype.card_fin]

/-- A one-unit shift in the expanded seed budget fits within the larger
square-root allowance of the selector recurrence. -/
theorem eventually_shifted_fifth :
    ∀ᶠ n : ℕ in atTop, ∀ base : ℕ, base ≤ width n (1/5:ℝ) → 1+base ≤ width n (1/2:ℝ) := by
  filter_upwards [eventually_ge_atTop 1,eventually_rpow_gap (by norm_num : (1/5:ℝ)<1/2) 2] with n hn gap
  intro base hbase
  apply Nat.le_floor
  have one := Real.one_le_rpow (by exact_mod_cast hn : 1≤(n:ℝ)) (by norm_num : (0:ℝ)≤1/5)
  have small : (base:ℝ) ≤ (n:ℝ)^(1/5:ℝ) :=
    (by exact_mod_cast hbase : (base:ℝ) ≤ (width n (1/5:ℝ):ℝ)).trans (Nat.floor_le (Real.rpow_nonneg (by positivity) _))
  push_cast
  linarith

/-- All calibrated count words fit starting from the concrete one-copy
channel and immutable padded descriptor. The fixed coefficient covers the
finite-direction catalog and the source's native record counts. -/
theorem eventually_seed_record_words {a x : ℕ} (s : EpochScales S a x) (headerFactor A : ℕ) :
    ∃ ω : ℝ, 0<ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → (r:ℝ) ≤ 2^((n:ℝ)^ω) →
      let q := Fintype.card (Cube D)
      let degree := Fintype.card (DeckGrid.Direction q)
      let start := CoverScale.initialDepth (Cube D) r n
      let depth := start-1
      let H := DeckGrid.seedChannelWidth n r q depth
      let dB := DeckGrid.seedDescriptionWidth n r q depth (headerFactor*logWidth r n)
        (BottomGridBank.bodyBudget (DeckGrid.seedBoxCapacity n r q depth degree))
      ∀ base : ℕ, base ≤ A*width n (s.α:ℝ)*(1+H+dB) →
        1+base ≤ width n (1/2:ℝ) ∧
        ∀ t < epochs s.τ n, ∀ j ≤ S.rounds, Fintype.card (Cube D → Deck (S.level (EnrichedOuter.offset S start t) j+1)) *
          innerCap S base t j ≤ (2*n*r)^2 := by
  let q := Fintype.card (Cube D)
  let _ : NeZero q := ⟨Fintype.card_pos.ne'⟩
  have α : 0<(s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have τ : 0<(s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have copies := s.rate (epochCopies_pos S) (epochGrowth_bounds S x).2.1
  have one : (s.τ:ℝ)*Real.logb 2 (1:ℕ) ≤ (s.α:ℝ)/10 := by simp; positivity
  obtain ⟨ω,hω,seed⟩ := DeckGrid.eventually_seed_sewn_caps α s.alpha_small τ s.tau_small
    (epochCopies_pos S) (C := 1) (by decide) (copies.trans (by linarith)) one q
    (Fintype.card (DeckGrid.Direction q)) headerFactor A
  refine ⟨ω,hω,?_⟩
  filter_upwards [seed,eventually_shifted_fifth,eventually_record_words S s] with n caps room words
  intro r hr hrmax q' degree start depth H dB base hbase
  have hstart : 1 ≤ start := Nat.succ_pos _
  have level : depth+1 = CoverScale.initialDepth (Fin q) r n := by
    rw [initialDepth_fin (D := D)]
    change start-1+1=start
    omega
  have baseFit := (caps r hr hrmax depth level 0 base (Nat.zero_le _) hbase).2.2
  exact ⟨room base baseFit,words r hr base (room base baseFit)⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
