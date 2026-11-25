import OAI.Computability.BorderVNP.PackedSelectedEpochOffset
import OAI.Computability.BorderVNP.ShortenEnrichedRecordClosure

/-! # Record capacities of the assigned public arrays before each selector

The input subdivision, every measured combining step, and final site motion
use their own factors from the selected schedule. Their product is bounded
by its single calibrated epoch factor. This supplies the selector count
range for any admissible input carrying the stated true local record bound.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover Epoch Epoch.Round Packing Shortening Diagonal TeamScales Filter
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- The local record multiplier incurred by the actual input subdivision. -/
noncomputable def subdivisionRecords :=
  1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) × Fin (hopCount S.budget S.radius))

/-- Common per-stage multiplier in the prepared path's calibrated epoch bound. -/
noncomputable def combiningRecords := 1+∑ i, (S.source.pattern i).record*S.fanIn

private theorem record_pos : 1 ≤ S.recordFactor := by
  unfold SiteSchedule.recordFactor Epoch.Round.epochRecordFactor
  change 0 < _
  positivity

/-- Bound on localRecords in the outer boundary state, which omits the extra unit used by RecordsWithin. -/
noncomputable def boundaryBudget (base t : ℕ) := S.recordFactor^t*(1+base)-1

/-- Per-tile RecordsWithin capacity at a physical inner state. -/
noncomputable def innerCap (base t j : ℕ) := (combiningRecords S)^j*subdivisionRecords S*(1+boundaryBudget S base t)

/-- The outer budget counts the preceding local cap with the epoch factor. -/
theorem boundary_add (base t : ℕ) : 1+boundaryBudget S base t = S.recordFactor^t*(1+base) := by
  have pos : 0 < S.recordFactor^t*(1+base) := Nat.mul_pos (Nat.one_le_pow _ _ (record_pos S)) (by omega)
  unfold boundaryBudget
  omega

/-- The initial rectangle uses exactly the starting tile's assigned budget. -/
theorem boundary_zero (base : ℕ) : boundaryBudget S base 0 = base := by simp [boundaryBudget]

/-- The same outer budget supplies the terminal motion's record factor. -/
theorem boundary_next (base t : ℕ) :
    S.recordFactor*(1+boundaryBudget S base t) = 1+boundaryBudget S base (t+1) := by
  rw [boundary_add,boundary_add,pow_succ']; ring

/-- The input subdivision starts the combining recurrence on the actual prior budget. -/
theorem inner_zero (base t : ℕ) : innerCap S base t 0 = subdivisionRecords S*(1+boundaryBudget S base t) := by
  simp [innerCap]

/-- The expanded child record bound is closed under every actual prepared-stage factor. -/
theorem inner_next (base t : ℕ) (i : Fin S.rounds) :
    (S.source.pattern i).record*S.fanIn*innerCap S base t i.val ≤ innerCap S base t (i.val+1) := by
  have stage := Finset.single_le_sum (f := fun j => (S.source.pattern j).record*S.fanIn)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have cap : (S.source.pattern i).record*S.fanIn ≤ combiningRecords S :=
    stage.trans (Nat.le_add_left _ 1)
  apply (Nat.mul_le_mul_right _ cap).trans_eq
  unfold innerCap
  rw [pow_succ']; ring

/-- Even the final inner table remains within the next outer capacity with its unit included. -/
theorem inner_le_boundary (base t j : ℕ) (hj : j ≤ S.rounds) :
    innerCap S base t j ≤ 1+boundaryBudget S base (t+1) := by
  rw [←boundary_next]
  have pos : 1 ≤ combiningRecords S := by unfold combiningRecords; omega
  have cap : combiningRecords S^j * subdivisionRecords S ≤ S.recordFactor := by
    calc
      _ ≤ combiningRecords S^S.rounds * subdivisionRecords S := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right pos hj)
      _ ≤ (1+S.finalCap)*(combiningRecords S^S.rounds*subdivisionRecords S) := Nat.le_mul_of_pos_left _ (by omega)
      _ = _ := by
        unfold SiteSchedule.recordFactor Epoch.Round.epochRecordFactor combiningRecords subdivisionRecords
        ring
  exact Nat.mul_le_mul_right _ cap

/-- Every inner expanded record capacity fits one processor word scale once
the one-copy bundle plus all its initial private payload fits the square-root scale. -/
theorem caps_le_length {a x : ℕ} (s : EpochScales S a x) {base n : ℕ} (hn : 1 ≤ n)
    (hb : 1+base ≤ TeamScales.width n (1/2:ℝ)) :
    (∀ t ≤ epochs s.τ n, 1+boundaryBudget S base t ≤ n) ∧
    ∀ t < epochs s.τ n, ∀ j ≤ S.rounds, innerCap S base t j ≤ n := by
  have rate := s.rate (record_pos S) (epochGrowth_bounds S x).2.2.2.1
  have τ : 0 ≤ (s.τ:ℝ) := by exact_mod_cast s.tau_pos.le
  have hg := epoch_growth_le (by exact_mod_cast record_pos S : 1 ≤ (S.recordFactor:ℝ)) hn τ rate
  have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hb' : ((1+base:ℕ):ℝ) ≤ (n:ℝ)^(1/2:ℝ) :=
    (by exact_mod_cast hb : ((1+base:ℕ):ℝ) ≤ (TeamScales.width n (1/2:ℝ):ℝ)).trans
      (Nat.floor_le (Real.rpow_nonneg (by positivity) _))
  have bound (t : ℕ) (ht : t ≤ epochs s.τ n) : 1+boundaryBudget S base t ≤ n := by
    rw [boundary_add]
    apply (Nat.cast_le (α := ℝ)).mp
    rw [Nat.cast_mul,Nat.cast_pow]
    have power := Nat.pow_le_pow_right (record_pos S) ht
    have hpow : (S.recordFactor:ℝ)^t ≤ (n:ℝ)^((s.α:ℝ)/10) :=
      (by exact_mod_cast power : (S.recordFactor:ℝ)^t ≤ (S.recordFactor:ℝ)^epochs s.τ n).trans hg
    calc
      _ ≤ (n:ℝ)^((s.α:ℝ)/10)*(n:ℝ)^(1/2:ℝ) := mul_le_mul hpow hb' (Nat.cast_nonneg _) (by positivity)
      _ = (n:ℝ)^((s.α:ℝ)/10+1/2) := (Real.rpow_add (zero_lt_one.trans_le hn') _ _).symm
      _ ≤ (n:ℝ)^1 := Real.rpow_le_rpow_of_exponent_le hn' (by linarith [s.alpha_small])
      _ = n := Real.rpow_one _
  exact ⟨bound,fun t ht j hj => (inner_le_boundary S base t j hj).trans (bound (t+1) ht)⟩

/-- The geometric product tile count and the calibrated capacity bound the
actual total cable width presented to each selected kernel's comparator. -/
theorem eventually_record_words {a x : ℕ} (s : EpochScales S a x) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → ∀ base : ℕ, 1+base ≤ TeamScales.width n (1/2:ℝ) →
      let T := epochs s.τ n
      let start := CoverScale.initialDepth (Cube D) r n
      ∀ t < T, ∀ j ≤ S.rounds,
        Fintype.card (Cube D → Deck (S.level (EnrichedOuter.offset S start t) j+1))*innerCap S base t j ≤ (2*n*r)^2 := by
  filter_upwards [eventually_offsets S s,eventually_ge_atTop 1] with n offsets hn
  intro r hr base hb T start t ht j hj
  let d := EnrichedOuter.offset S start t
  obtain ⟨deep,vol⟩ := offsets r hr
  have old := EnrichedOuter.levels S deep ht
  let word := fun i => (S.source.pattern i).word
  have high := Adaptive.Levels.le_start word (S.high d-S.drop) S.last j
  change S.level d j ≤ S.level d 0 at high
  rw [S.start_level,old.2.2] at high
  have shallow : S.level d j ≤ start := high.trans (Nat.sub_le ..)
  have tile := PublicCapacity.tiles_mono (Cube D) (Nat.succ_le_succ shallow)
  have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have expo : (n:ℝ)^(9/10:ℝ) ≤ n := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (9/10:ℝ) ≤ 1)
  have vnat : CoverScale.sites (Cube D) start ≤ r*n := by
    exact_mod_cast vol.trans (mul_le_mul_of_nonneg_left expo (Nat.cast_nonneg r))
  have vsize : Fintype.card (Cube D → Deck (S.level d j+1)) ≤ 2*n*r :=
    tile.trans (vnat.trans (by nlinarith))
  have count := (caps_le_length S s hn hb).2 t ht j hj
  have nfit : n ≤ 2*n*r := by nlinarith [Nat.mul_le_mul_left n hr]
  exact (Nat.mul_le_mul vsize (count.trans nfit)).trans_eq (sq _).symm

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
