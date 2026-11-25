import OAI.Computability.BorderVNP.PackedHistoryNormalizedMachine
import OAI.Computability.BorderVNP.PackedSiteDecay
import OAI.Computability.BorderVNP.ShortenPublicPaddedWords

/-! # Normalized physical width along the actual named execution

The true named child tuple determines the program's retained directories,
private metadata and public terminal motion. Each true profile obeys the
half-potential bound at the measured depths, so the same per-copy estimate
holds even if equal unlabelled packs carry different physical pin arrays.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter

open Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Packing Adaptive PublicCapacity PhysicalEpochs Filter TeamScales Finset
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}

private theorem volume_le {start T t : ℕ} (deep : S.floor+1+S.drop*T ≤ start) (ht : t ≤ T) :
    CoverScale.sites (Cube D) (depth S start t) ≤ CoverScale.sites (Cube D) start := by
  have hmul := Nat.mul_le_mul_left S.drop ht
  let d := depth S start t
  have hd : 1 ≤ d := by dsimp [d,depth]; omega
  have hadd : d + S.drop*t = start := by dsimp [d,depth]; omega
  conv_rhs => rw [← hadd,CoverScale.sites_add _ hd]
  exact Nat.le_mul_of_pos_left _ (pow_pos (zero_lt_one.trans (CoverScale.one_lt_factor _)) _)

namespace Machine

variable {start T : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {shape : ℕ → Shape} {W : ℕ → Type}
variable [∀ t, Fintype (W t)] {deep : S.floor+1+S.drop*T ≤ start}
variable {good : ∀ t, State S start P bits shape W t → Prop}
variable {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)] {w : ℕ → ℕ → ℕ}
variable (M : Machine.{_,u} deep good V w) (bottom : Admissible good 0)

set_option maxHeartbeats 1000000 in
/-- The normalized site potential of every returned named state after t
epochs. The geometric cost is evaluated on that state's actual physical
routes. -/
theorem normalizedPotential {b : ℕ} (hb : 0 < b) (t : ℕ) (q : (packHistory bottom M.epoch t).Index) :
    ((packHistory bottom M.epoch t).term q).val.route.potential S.weight / ((b:ℝ)*(fan S : ℝ)^t) ≤
      bottom.val.route.potential S.weight / b / 2^t + 2*(S.error*CoverScale.sites (Cube D) start) := by
  let I (t : ℕ) (s : Admissible good t) := s.val.route.potential S.weight
  have hk : 0 < fan S := pow_pos S.positiveFanIn _
  apply history_potential_bound bottom M.epoch hk hb I (mul_nonneg S.error_pos.le (Nat.cast_nonneg _)) _ t q
  intro n c
  by_cases hn : n<T
  · let E := M n hn
    rw [show M.epoch n c = E.choice c from dite_eq_left hn]
    intro j
    have h := E.epochBound c j
    have hden : (S.fanIn:ℝ)^S.rounds = (fan S : ℝ) := (Nat.cast_pow S.fanIn S.rounds).symm
    rw [hden] at h
    apply h.trans
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ S.error_pos.le
    apply Nat.cast_le.mpr
    exact (card_eq_sites (Cube D) (depth S start n) _).le.trans (volume_le deep hn.le)
  · let Z : ProfileSum (Admissible good (n+1)) := ⟨Empty,inferInstance,Empty.elim⟩
    rw [show M.epoch n c = Z from dite_eq_right hn]
    exact fun j => Empty.elim j

end Machine

/-- Uniform exterior bound for every accepted enriched physical history.
The bottom-state coefficient and the schedule are chosen before the batch
size, the particular pin array and the adaptive geometric program. -/
theorem eventuallyNamedWidth {τ : ℝ} (hτ : 0 < τ) (hτ' : τ < 1/2) (uLog : ℕ) (S : SiteSchedule e) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A ε : ℝ, 0 ≤ A → 0 < ε →
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2^((n : ℝ)^ω) →
    ∀ {start b : ℕ}, 0 < b → (CoverScale.sites (Cube D) start : ℝ) ≤ r*(n : ℝ)^(9/10 : ℝ) →
    ∀ {P : Type} [Fintype P] {bits : P → ℕ} {shape : ℕ → Shape} {W : ℕ → Type} [∀ t, Fintype (W t)]
      {deep : S.floor+1+S.drop*epochs τ n ≤ start} {good : ∀ t, State S start P bits shape W t → Prop}
      {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)] {w : ℕ → ℕ → ℕ}
      (M : Machine.{_,u} deep good V w) (bottom : Admissible good 0),
      bottom.val.route.potential S.weight / b ≤ A*volume τ r n*(logWidth r n : ℝ)^uLog →
      ∀ q : (packHistory bottom M.epoch (epochs τ n)).Index,
        ((packHistory bottom M.epoch (epochs τ n)).term q).val.route.nonlocalWidth /
          ((b : ℝ)*(fan S : ℝ)^epochs τ n) ≤ ε*exterior (τ/5) r n := by
  obtain ⟨ω,hω,decay⟩ := eventually_charged_width hτ hτ' uLog
  refine ⟨ω,hω,?_⟩
  intro A ε hA hε
  have hcoef : 0 ≤ A+2*S.error := by linarith [S.error_pos]
  filter_upwards [eventually_ge_atTop 1,decay (A+2*S.error) S.error ε hcoef S.error_pos.le hε] with n hn hd
  intro r hr hr' start b hb hv P _ bits shape W _ deep good V _ w M bottom hbot q
  let loss := S.error*r*(n : ℝ)^(9/10 : ℝ)
  let x := bottom.val.route.potential S.weight / b
  let f (t : ℕ) : ℝ := x/2^t + 2*loss
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hL : 1 ≤ logWidth r n := by
    rw [public_logWidth]
    exact (show 1 = Nat.clog 2 2 by decide).le.trans (Nat.clog_mono_right 2 (by nlinarith))
  have hpower : r*(n : ℝ)^(9/10 : ℝ) ≤ volume τ r n*(logWidth r n : ℝ)^uLog := by
    apply le_trans _ (le_mul_of_one_le_right (show 0 ≤ volume τ r n by unfold volume; positivity)
      (one_le_pow₀ (by exact_mod_cast hL)))
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn' (by linarith)) (Nat.cast_nonneg _)
  have hf : f 0 ≤ (A+2*S.error)*volume τ r n*(logWidth r n : ℝ)^uLog := by
    have h := mul_le_mul_of_nonneg_left hpower (show 0 ≤ 2*S.error by linarith [S.error_pos])
    dsimp [f,loss,x]
    simp only [pow_zero,div_one]
    linarith only [hbot,h]
  have hs (j : ℕ) (_ : j < epochs τ n) : f (j+1) ≤ f j / 2 + S.error*r*(n : ℝ)^(9/10 : ℝ) := by
    apply le_of_eq
    dsimp [f,loss]; rw [pow_succ]; ring
  have hh := hd r hr hr' f hf hs
  have hbnd := M.normalizedPotential bottom hb _ q
  apply le_trans _ hh
  apply le_trans _ (hbnd.trans _)
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact le_add_of_nonneg_right (mul_nonneg S.weight_pos.le
      ((packHistory bottom M.epoch (epochs τ n)).term q).val.route.nonneg_width_concentration.2)
  · apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [loss,mul_assoc] using mul_le_mul_of_nonneg_left hv S.error_pos.le

end PackedHistoryCircuit.Normalized.EnrichedOuter

end BorderVNP
end Computability
end OAI
