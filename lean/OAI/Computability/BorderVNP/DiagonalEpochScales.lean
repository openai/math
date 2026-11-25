import OAI.Computability.BorderVNP.DiagonalFixedCube
import OAI.Computability.BorderVNP.PackedBankInheritedDenseEpochs
import OAI.Computability.BorderVNP.ShortenDenseSiteEpoch
import OAI.Computability.BorderVNP.ShortenEpochRoundDenseExecutionRecords
import OAI.Computability.BorderVNP.ShortenPublicPaddedCapacity
import OAI.Computability.BorderVNP.ShortenPublicScheduleLevels

/-! # Choosing the two epoch exponents for the calibrated public schedule

The record multiplier, cover loss, copy multiplicity, and sparse row multiplier
come from the same finite schedule. The choices accommodate any further fixed
growth factor of the public program before any input length is supplied.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing PackedHistoryCircuit.Normalized Packing Cover Epoch
open scoped Classical

variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m}

/-- The number of source copies combined by the complete epoch. -/
def epochCopies (S : SiteSchedule e) := S.fanIn ^ S.rounds

/-- The multiplicative loss of tile count from the actual congruence drop. -/
def epochCoverLoss (S : SiteSchedule e) := CoverScale.factor (Cube D) ^ S.drop

/-- The row expansion including subdivision stripes and all seed rectangles. -/
noncomputable def epochRowFactor (S : SiteSchedule e) :=
  Shortening.PublicCapacity.epochFactor e S.fanIn S.rounds ⌈S.budget / S.radius⌉₊
    (Finset.univ.sup fun i => Fintype.card (S.source.pattern i).bins.Bin)

/-- The product inside the logarithm in (7.1), enlarged to cover the public
rectangular arrays and an additional fixed program multiplier. -/
noncomputable def epochGrowth (S : SiteSchedule e) (extra : ℕ) :=
  max (2 * epochCopies S * epochCoverLoss S * (1+S.recordFactor))
    (max (epochRowFactor S) (max (S.bankRecordFactor+1) (extra+1)))

theorem epochCopies_pos (S : SiteSchedule e) : 1 ≤ epochCopies S :=
  Nat.one_le_pow _ _ S.positiveFanIn

theorem epochCoverLoss_pos (S : SiteSchedule e) : 1 ≤ epochCoverLoss S :=
  Nat.one_le_pow _ _ (CoverScale.one_lt_factor (Cube D)).le

theorem epochGrowth_bounds (S : SiteSchedule e) (extra : ℕ) :
    1 ≤ epochGrowth S extra ∧ epochCopies S ≤ epochGrowth S extra ∧
    epochCoverLoss S ≤ epochGrowth S extra ∧ S.recordFactor ≤ epochGrowth S extra ∧
    epochRowFactor S ≤ epochGrowth S extra ∧ extra ≤ epochGrowth S extra := by
  have hc := epochCopies_pos S
  have hq := epochCoverLoss_pos S
  have h1 : epochCopies S ≤ 2 * epochCopies S * epochCoverLoss S :=
    (show epochCopies S ≤ 2*epochCopies S by omega).trans (Nat.le_mul_of_pos_right _ hq)
  have h2 : epochCoverLoss S ≤ 2 * epochCopies S * epochCoverLoss S :=
    Nat.le_mul_of_pos_left _ (by omega)
  let M := 2 * epochCopies S * epochCoverLoss S * (1+S.recordFactor)
  have h3 : 2 * epochCopies S * epochCoverLoss S ≤ M :=
    Nat.le_mul_of_pos_right _ (by omega)
  have h4 : 1+S.recordFactor ≤ M := Nat.le_mul_of_pos_left _ (by omega)
  have h5 : M ≤ epochGrowth S extra := le_max_left ..
  have h6 : max (epochRowFactor S) (max (S.bankRecordFactor+1) (extra+1)) ≤ epochGrowth S extra := le_max_right ..
  omega

/-- Conditions on the rational parameters picked before the stretch exponents. -/
structure EpochScales (S : SiteSchedule e) (a extra : ℕ) where
  /-- Exponent of the initial pack multiplicity. -/
  α : ℚ
  /-- Epoch rate per binary logarithm of processor length. -/
  τ : ℚ
  alpha_pos : 0 < α
  alpha_cube : (α : ℝ) * a < 1 / 10^6
  alpha_small : (α : ℝ) < 1/1000
  tau_pos : 0 < τ
  tau_small : (τ : ℝ) < α/100
  growth : (τ : ℝ) * Real.logb 2 (epochGrowth S extra) < α/10

/-- All growth factors are chosen from the calibrated schedule before the
rational parameters. The cube dimension can be any previously chosen positive integer. -/
theorem exists_epochScales (S : SiteSchedule e) (a extra : ℕ) (ha : 1 ≤ a) :
    Nonempty (EpochScales S a extra) := by
  have hG : 1 ≤ (epochGrowth S extra : ℝ) := by exact_mod_cast (epochGrowth_bounds S extra).1
  obtain ⟨α,τ,ha0,ha1,ht0,ht1,hg⟩ := TeamScales.exists_epoch_scales a ha hG
  have harp : 0 < (α : ℝ) := by exact_mod_cast ha0
  have ar : 1 ≤ (a : ℝ) := by exact_mod_cast ha
  have ax : (α : ℝ) < (1/10)/(10^5*(a:ℝ)) := by
    have lifted := (Rat.cast_lt (K := ℝ)).mpr ha1
    push_cast at lifted
    exact lifted
  have ax' := (lt_div_iff₀ (show 0 < 10^5*(a:ℝ) by positivity)).mp ax
  have cube : (α : ℝ)*a < 1/10^6 := by linarith
  have small := mul_le_mul_of_nonneg_left ar harp.le
  exact ⟨⟨α,τ,ha0,cube,by linarith,ht0,by exact_mod_cast ht1,hg⟩⟩

/-- The same saving applies to every fixed positive subfactor of (7.1). -/
theorem EpochScales.rate {S : SiteSchedule e} {a extra : ℕ} (s : EpochScales S a extra)
    {c : ℕ} (hc : 1 ≤ c) (bound : c ≤ epochGrowth S extra) :
    (s.τ : ℝ)*Real.logb 2 c ≤ (s.α : ℝ)/10 := by
  have hτ : 0 ≤ (s.τ : ℝ) := by exact_mod_cast s.tau_pos.le
  have hlog := Real.logb_le_logb_of_le (by norm_num : 1 < (2:ℝ))
    (by exact_mod_cast (zero_lt_one.trans_le hc) : 0 < (c:ℝ))
    (by exact_mod_cast bound : (c:ℝ) ≤ epochGrowth S extra)
  exact (mul_le_mul_of_nonneg_left hlog hτ).trans s.growth.le

/-- The enlarged private descriptors carried by the dense bank construction
use the same saving as the original public records. -/
theorem EpochScales.bank_rate {S : SiteSchedule e} {a extra : ℕ} (s : EpochScales S a extra) :
    (s.τ:ℝ)*Real.logb 2 (S.bankRecordFactor+1 : ℕ) ≤ (s.α:ℝ)/10 := by
  apply s.rate (by omega)
  exact (le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..))

end Diagonal

end BorderVNP
end Computability
end OAI
