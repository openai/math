import OAI.Computability.BorderVNP.PackedBankEpochFactors
import OAI.Computability.BorderVNP.PackedSeedSelectedCaps
import OAI.Computability.BorderVNP.DiagonalEpochScales
import OAI.Computability.BorderVNP.CellVisitWidth

/-! # Word room for the actual subdivided and stored banks at selected epochs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover Epoch Shortening Packing Packing.CoverScale Packing.DeckGrid Diagonal TeamScales Filter
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- The genuine full-program epoch multiplier is included in the common selected
scale by the published extra-factor budget. -/
theorem publicProgramFactor_rate {a x : ℕ} (s : EpochScales S a x) (reserved : S.publicProgramFactor ≤ x) :
    (s.τ : ℝ)*Real.logb 2 S.publicProgramFactor ≤ (s.α : ℝ)/10 := by
  have hpos : 0 < S.publicProgramFactor := by unfold SiteSchedule.publicProgramFactor SiteSchedule.bankRecordFactor Epoch.Round.epochRecordFactor; positivity
  exact s.rate hpos (reserved.trans (epochGrowth_bounds S x).2.2.2.2.2)

private theorem room_of_exponent {a x : ℕ} (s : EpochScales S a x) (β : ℝ) (ha : (s.α : ℝ) ≤ β) (small : β < 1/1000)
    (growth : (s.τ : ℝ)*Real.logb 2 S.publicProgramFactor ≤ β/10)
    (headerFactor : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2^((n:ℝ)^ω) →
      ∀ d, d+1 = initialDepth (Fin (Fintype.card (Cube D))) r n →
      let q := Fintype.card (Cube D)
      let deg := Fintype.card (Direction q)
      let H := seedChannelWidth n r q d
      let cap := seedBoxCapacity n r q d deg
      let dB := seedDescriptionWidth n r q d (headerFactor*logWidth r n) (BottomGridBank.bodyBudget cap)
      let b := width n (s.α : ℝ)
      let T := epochs (s.τ : ℝ) n
      let M := S.publicProgramFactor^T*baseMass deg cap H b dB
      5*b*(S.publicProgramFactor^T*seedPublicBase deg) ≤ width n (1/100) ∧
        7*M ≤ width n (1/5) ∧ 7*M < 2^(60*logWidth r n) := by
  let q := Fintype.card (Cube D)
  let _ : NeZero q := ⟨Fintype.card_pos.ne'⟩
  have hα : 0 < (s.α : ℝ) := by exact_mod_cast s.alpha_pos
  have hτ : 0 < (s.τ : ℝ) := by exact_mod_cast s.tau_pos
  have hc : 0 < S.publicProgramFactor := by unfold SiteSchedule.publicProgramFactor SiteSchedule.bankRecordFactor Epoch.Round.epochRecordFactor; positivity
  have fanRate := s.rate (epochCopies_pos S) (epochGrowth_bounds S x).2.1
  obtain ⟨ω,hω,actual⟩ := eventually_seed_actual_caps (hα.trans_le ha) small hτ (s.tau_small.trans_le (by linarith)) (epochCopies_pos S)
    hc (fanRate.trans (by linarith)) growth q headerFactor
  refine ⟨ω,hω,?_⟩
  filter_upwards [actual,eventually_ge_atTop 1] with n caps hn
  intro r hr maxR d hd q' deg H cap dB b T M
  obtain ⟨hp,he,_⟩ := caps r hr maxR d hd
  have copies : b ≤ width n β := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) ha)
  have mass : baseMass deg cap H b dB ≤ baseMass deg cap H (width n β) dB := Nat.add_le_add_left (Nat.mul_le_mul_right _ copies) _
  have smaller := (Nat.mul_le_mul_left 7 (Nat.mul_le_mul_left (S.publicProgramFactor^T) mass)).trans he
  refine ⟨(Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 5 copies)).trans hp,smaller,smaller.trans_lt ?_⟩
  have rounded : width n (1/5) ≤ n := Nat.floor_le_of_le
    ((Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ) ≤ n) (by norm_num : (1/5:ℝ) ≤ 1)).trans_eq
      (Real.rpow_one _))
  have bits := Nat.size_le.mp (CellMacro.Generator.size_le_logWidth n r hr)
  exact rounded.trans_lt (bits.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))

/-- The actual propagated expanded bank fits the native word, simultaneously
at every processor count and every selected cover level. The bound covers
twice any intermediate cap and three times the terminal directory cap. -/
theorem eventually_bank_word_room {a x : ℕ} (s : EpochScales S a x) (reserved : S.publicProgramFactor ≤ x)
    (headerFactor : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2^((n:ℝ)^ω) →
      ∀ d, d+1 = initialDepth (Fin (Fintype.card (Cube D))) r n →
      let q := Fintype.card (Cube D)
      let deg := Fintype.card (Direction q)
      let H := seedChannelWidth n r q d
      let cap := seedBoxCapacity n r q d deg
      let dB := seedDescriptionWidth n r q d (headerFactor*logWidth r n) (BottomGridBank.bodyBudget cap)
      let b := width n (s.α : ℝ)
      let T := epochs (s.τ : ℝ) n
      let M := S.publicProgramFactor^T*baseMass deg cap H b dB
      5*b*(S.publicProgramFactor^T*seedPublicBase deg) ≤ width n (1/100) ∧
        7*M ≤ width n (1/5) ∧ 7*M < 2^(60*logWidth r n) :=
  room_of_exponent S s _ le_rfl s.alpha_small (publicProgramFactor_rate S s reserved) headerFactor

/-- The complete per-epoch stored-program multiplier obeys the selected
growth bound, including the subdivision surcharge. -/
theorem calibrated_program_rate {a x : ℕ} (s : EpochScales S a x) :
    (s.τ : ℝ)*Real.logb 2 S.publicProgramFactor ≤ 3*(s.α : ℝ)/10 := by
  have hτ : 0 < (s.τ : ℝ) := by exact_mod_cast s.tau_pos
  have hb : 0 < S.bankRecordFactor := by unfold SiteSchedule.bankRecordFactor Epoch.Round.epochRecordFactor; positivity
  have bankLe := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (show (0 : ℝ) < S.bankRecordFactor by exact_mod_cast hb)
    (show (S.bankRecordFactor : ℝ) ≤ (S.bankRecordFactor+1 : ℕ) by exact_mod_cast Nat.le_succ S.bankRecordFactor)
  have bank := (mul_le_mul_of_nonneg_left bankLe hτ.le).trans s.bank_rate
  have c : Real.logb 2 1040 ≤ 11 := calc
    _ ≤ Real.logb 2 ((2 : ℝ)^11) := Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
    _ = 11 := by rw [Real.logb_pow]; norm_num
  calc
    (s.τ : ℝ)*Real.logb 2 S.publicProgramFactor =
        (s.τ : ℝ)*(Real.logb 2 1040+Real.logb 2 S.bankRecordFactor) := by
      rw [SiteSchedule.publicProgramFactor,Nat.cast_mul,Real.logb_mul (by norm_num) (by exact_mod_cast hb.ne')]
      norm_num
    _ ≤ (s.τ : ℝ)*11+(s.α : ℝ)/10 := by rw [mul_add]; exact add_le_add (mul_le_mul_of_nonneg_left c hτ.le) bank
    _ ≤ 3*(s.α : ℝ)/10 := by linarith [s.tau_small]


/-- For every positive cube dimension the fixed subdivision multiplier contributes
less than eleven binary digits per epoch. An enlarged auxiliary exponent absorbs this term while preserving the
original seed multiplicity and the prescribed public and private thresholds. -/
theorem eventually_calibrated_bank_word_room {a x : ℕ} (s : EpochScales S a x) (dim : 1 ≤ a)
    (headerFactor : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2^((n:ℝ)^ω) →
      ∀ d, d+1 = initialDepth (Fin (Fintype.card (Cube D))) r n →
      let q := Fintype.card (Cube D)
      let deg := Fintype.card (Direction q)
      let H := seedChannelWidth n r q d
      let cap := seedBoxCapacity n r q d deg
      let dB := seedDescriptionWidth n r q d (headerFactor*logWidth r n) (BottomGridBank.bodyBudget cap)
      let b := width n (s.α : ℝ)
      let T := epochs (s.τ : ℝ) n
      let M := S.publicProgramFactor^T*baseMass deg cap H b dB
      5*b*(S.publicProgramFactor^T*seedPublicBase deg) ≤ width n (1/100) ∧
        7*M ≤ width n (1/5) ∧ 7*M < 2^(60*logWidth r n) := by
  have hα : 0 < (s.α : ℝ) := by exact_mod_cast s.alpha_pos
  have αcube := s.alpha_cube
  have adim := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ a by exact_mod_cast dim) hα.le
  exact room_of_exponent S s (3*(s.α : ℝ)) (by linarith) (by linarith) (calibrated_program_rate S s) headerFactor

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
