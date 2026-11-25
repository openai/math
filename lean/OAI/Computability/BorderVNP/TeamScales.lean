import OAI.Computability.VPVNP.CompressionParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Team and processor sizes in the border diagonal

Equations (7.1) and (7.2) of *An explicit VNP family requires superpolynomial
border circuit size over every field* fix the epochs and the external communication
budget. The scale estimates here include the rounding of every processor's time block
in Lemma 7.1. Thresholds for the input length are uniform in the team size.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamScales

open Filter

/-- Epochs in the shortening and packing procedure. -/
noncomputable def epochs (τ : ℝ) (n : ℕ) : ℕ := VPVNP.Compression.blockCount τ n

/-- Integral bit count at a real exponent. -/
noncomputable def width (n : ℕ) (e : ℝ) : ℕ := ⌊(n : ℝ) ^ e⌋₊

/-- Equation (7.1), with pack multiplicity `K` and initial batch `⌊n^α⌋`. -/
noncomputable def teams (α τ : ℝ) (K n : ℕ) : ℕ := width n α * K ^ epochs τ n

/-- Allowed bit-network volume in (7.2). -/
noncomputable def volume (τ : ℝ) (r n : ℕ) : ℝ := r * (n : ℝ) ^ (1 + τ / 20)

/-- External communication budget in (7.2), with `ξ = τ/5`. -/
noncomputable def exterior (ξ : ℝ) (r n : ℕ) : ℕ := r * width n (1 - ξ)

/-- Width of each processor's literal. -/
noncomputable def literal (α : ℝ) (n : ℕ) : ℕ := width n (1 - α / 3)

/-- Direct physical width from each processor to its counterpart on another team. -/
noncomputable def link (ξ : ℝ) (R n : ℕ) : ℕ := width n (1 - ξ) / R

/-- One processor's time block in the proof of Lemma 7.1. -/
noncomputable def block (ξ : ℝ) (n : ℕ) : ℕ := width n (1 - ξ / 3)

/-- Logical tick limit in Lemma 7.1, rounded after multiplying by the team size. -/
noncomputable def ticks (ξ : ℝ) (r n : ℕ) : ℕ := ⌊(r : ℝ) * (n : ℝ) ^ (1 - ξ / 2)⌋₊

/-- The initial cube dimension and selector tolerance can be fixed before choosing
the host geometry or the processor length. -/
theorem exists_cube_dimension :
    ∃ k : ℕ, ∃ η : ℝ, 0 < η ∧
      100 * (2 * ((2 : ℝ) ^ k) ^ (-1 / 2 : ℝ) + η) < 1 / 10 ^ 6 := by
  refine ⟨64, 1 / 10 ^ 10, by norm_num, ?_⟩
  have hpow : ((2 : ℝ) ^ (64 : ℕ)) ^ (-1 / 2 : ℝ) = ((2 : ℝ) ^ (32 : ℕ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [Real.rpow_neg]
  rw [hpow]
  norm_num

/-- Rational choices of the two shortening scales in §7.1, with `β = 1/10`.
Here `G` is the combined per-epoch growth constant inside the binary logarithm. -/
theorem exists_epoch_scales (a : ℕ) (ha : 0 < a) {G : ℝ} (hG : 1 ≤ G) :
    ∃ α τ : ℚ, 0 < α ∧ α < (1 / 10) / (10 ^ 5 * a) ∧ 0 < τ ∧ τ < α / 100 ∧
      (τ : ℝ) * Real.logb 2 G < (α : ℝ) / 10 := by
  let α : ℚ := (1 / 10) / (2 * 10 ^ 5 * a)
  have ha' : 0 < (a : ℚ) := by exact_mod_cast ha
  have hα : 0 < α := by dsimp [α]; positivity
  have hαsmall : α < (1 / 10) / (10 ^ 5 * a) := by
    dsimp [α]
    apply div_lt_div_of_pos_left (by norm_num) (by positivity)
    nlinarith
  have hαr : 0 < (α : ℝ) := by exact_mod_cast hα
  have hlog := Real.logb_nonneg (by norm_num : 1 < (2 : ℝ)) hG
  have hden : 0 < 1 + Real.logb 2 G := by linarith
  obtain ⟨τ, hτ, hbounds⟩ := exists_rat_btwn (lt_min (show 0 < (α : ℝ) / 100 by positivity)
    (div_pos (show 0 < (α : ℝ) / 10 by positivity) hden))
  have ⟨ht, hg⟩ := lt_min_iff.mp hbounds
  refine ⟨α, τ, hα, hαsmall, Rat.cast_pos.mp hτ, ?_, ?_⟩
  · exact_mod_cast ht
  · have := (lt_div_iff₀ hden).mp hg
    linarith

/-- A bound for any multiplicative growth factor after the rounded number of epochs. -/
theorem epoch_growth_le {k τ e : ℝ} {n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hτ : 0 ≤ τ) (he : τ * Real.logb 2 k ≤ e) : k ^ epochs τ n ≤ (n : ℝ) ^ e := by
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos := zero_lt_one.trans_le hn'
  rw [epochs, VPVNP.Compression.blockCount, ← Real.rpow_natCast]
  calc
    _ ≤ k ^ (τ * Real.logb 2 n) := Real.rpow_le_rpow_of_exponent_le hk
      (Nat.floor_le (mul_nonneg hτ (Real.logb_nonneg (by norm_num) hn')))
    _ = (n : ℝ) ^ (τ * Real.logb 2 k) := by
      nth_rw 1 [← Real.rpow_logb (by norm_num : 0 < (2 : ℝ)) (by norm_num : (2 : ℝ) ≠ 1)
        (zero_lt_one.trans_le hk)]
      rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)),
        show Real.logb 2 k * (τ * Real.logb 2 n) = Real.logb 2 n * (τ * Real.logb 2 k) by ring,
        Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)), Real.rpow_logb (by norm_num) (by norm_num) hnpos]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn' he

/-- The number of teams is at most `n^(2α)` even with the integer roundings. -/
theorem teams_le {α τ : ℝ} {K n : ℕ} (hK : 1 ≤ K) (hn : 1 ≤ n)
    (hτ : 0 ≤ τ) (hα : τ * Real.logb 2 K ≤ α) :
    (teams α τ K n : ℝ) ≤ (n : ℝ) ^ (2 * α) := by
  rw [teams, width, Nat.cast_mul, Nat.cast_pow, two_mul, Real.rpow_add (by exact_mod_cast hn : 0 < (n : ℝ))]
  exact mul_le_mul (Nat.floor_le (Real.rpow_nonneg (by positivity) _))
    (epoch_growth_le (by exact_mod_cast hK) hn hτ hα) (by positivity) (by positivity)

/-- Dividing the exterior budget among all other teams cannot exceed it. -/
theorem exterior_links_le (ξ : ℝ) (R n : ℕ) : (R - 1) * link ξ R n ≤ width n (1 - ξ) :=
  (Nat.mul_le_mul_right _ (Nat.sub_le R 1)).trans (Nat.mul_div_le _ _)

/-- Each exterior link retains the indicated power of the input length. -/
theorem link_lower {ξ e : ℝ} {R n : ℕ} (hn : 1 ≤ n) (hR : 0 < R)
    (hRe : (R : ℝ) ≤ (n : ℝ) ^ e) :
    width n (1 - ξ - e) ≤ link ξ R n := by
  rw [link, Nat.le_div_iff_mul_le hR, width, width]
  apply Nat.le_floor
  rw [Nat.cast_mul]
  calc
    _ ≤ (n : ℝ) ^ (1 - ξ - e) * (n : ℝ) ^ e := mul_le_mul
      (Nat.floor_le (Real.rpow_nonneg (by positivity) _)) hRe (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by exact_mod_cast hn : 0 < (n : ℝ)), sub_add_cancel]

/-- Literal, optional pin field, and physical exterior fields give at most three blocks
of initialization records per processor. -/
theorem input_fields_le {α ξ : ℝ} {n : ℕ} (hn : 1 ≤ n) (hξ : 0 ≤ ξ) (hα : ξ ≤ α)
    (R : ℕ) : 2 * literal α n + (R - 1) * link ξ R n ≤ 3 * block ξ n := by
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hw : ∀ {a b : ℝ}, a ≤ b → width n a ≤ width n b :=
    fun hab => Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hn' hab)
  have ht : literal α n ≤ block ξ n := hw (by linarith)
  have hl := (exterior_links_le ξ R n).trans (hw (show 1 - ξ ≤ 1 - ξ / 3 by linarith))
  change _ ≤ 3 * width n (1 - ξ / 3)
  change literal α n ≤ width n (1 - ξ / 3) at ht
  omega

/-- Any fixed coefficient is eventually absorbed by increasing the exponent by a positive amount. -/
theorem eventually_rpow_gap {a b : ℝ} (hab : a < b) (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by
  have h := (tendsto_rpow_atTop (sub_pos.mpr hab)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [h.eventually_ge_atTop c, eventually_ge_atTop 1] with n hc hn
  calc
    _ ≤ (n : ℝ) ^ (b - a) * (n : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [← Real.rpow_add (by exact_mod_cast hn : 0 < (n : ℝ)), sub_add_cancel]

/-- The team can schedule the logical tick budget despite unused ticks at each handoff.
The length threshold is independent of `r`, including a one-processor team. -/
theorem eventually_ticks_fit {ξ : ℝ} (hξ : 0 < ξ) (hξ' : ξ < 3 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 0 < r →
      ticks ξ r n < r * (block ξ n - width n (1 / 2)) := by
  have hbig : 0 < 1 - ξ / 3 := by linarith
  filter_upwards [eventually_rpow_gap (show 1 - ξ / 2 < 1 - ξ / 3 by linarith) 4,
    eventually_rpow_gap (show 1 / 2 < 1 - ξ / 3 by linarith) 4,
    eventually_rpow_gap hbig 4] with n htime hidle hround
  rw [Real.rpow_zero, mul_one] at hround
  have hround' := Nat.lt_floor_add_one ((n : ℝ) ^ (1 - ξ / 3))
  have hidle' := Nat.floor_le (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)) (1 / 2))
  change (width n (1 / 2) : ℝ) ≤ _ at hidle'
  change _ < (block ξ n : ℝ) + 1 at hround'
  have hpos := Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)) (1 - ξ / 2)
  have hslack : (n : ℝ) ^ (1 - ξ / 2) + width n (1 / 2) < block ξ n := by linarith
  have hle : width n (1 / 2) ≤ block ξ n := by
    exact_mod_cast (show (width n (1 / 2) : ℝ) ≤ block ξ n by linarith)
  intro r hr
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have ht := Nat.floor_le (mul_nonneg hr'.le hpos)
  change (ticks ξ r n : ℝ) ≤ (r : ℝ) * (n : ℝ) ^ (1 - ξ / 2) at ht
  have hfit := ht.trans_lt (mul_lt_mul_of_pos_left (lt_sub_iff_add_lt.mpr hslack) hr')
  rwa [← Nat.cast_sub hle, ← Nat.cast_mul, Nat.cast_lt] at hfit

/-- For any fixed number of literal fields, all their deliveries are eventually
smaller than the exterior budget, uniformly in the team size. -/
theorem eventually_literals_le {α ξ : ℝ} (h : ξ < α / 3) (c : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, c * r * literal α n ≤ exterior ξ r n := by
  filter_upwards [eventually_rpow_gap (show 1 - α / 3 < 1 - ξ by linarith) c] with n hn
  have hc : c * literal α n ≤ width n (1 - ξ) := by
    apply Nat.le_floor
    rw [Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_left
      (Nat.floor_le (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)) (1 - α / 3)))
      (by positivity : 0 ≤ (c : ℝ))).trans hn
  intro r
  simpa [exterior, mul_left_comm, mul_assoc] using Nat.mul_le_mul_left r hc

/-- With a positive pack exponent the team graph eventually contains arbitrarily
many vertices. This ensures there are intermediate teams for physical relay routing. -/
theorem eventually_many_teams {α : ℝ} (hα : 0 < α) (τ : ℝ) {K : ℕ} (hK : 0 < K) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, m ≤ teams α τ K n := by
  have h := (tendsto_rpow_atTop hα).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [h.eventually_ge_atTop (m : ℝ)] with n hn
  exact (Nat.le_floor hn).trans (Nat.le_mul_of_pos_right _ (pow_pos hK _))

/-- Rounded binary logarithm for address lengths and fixed powers of index overhead. -/
noncomputable def logWidth (r n : ℕ) : ℕ := ⌈Real.logb 2 (2 * (n : ℝ) * r)⌉₊

/-- Choose the exponent of the admissible team size after fixing all logarithmic costs.
The estimate includes the rounding needed to store the words. In §7.1 one uses
`γ = Δ/100` and the largest of the finitely many total degrees of these costs. -/
theorem exists_polylog_budget (D : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r →
      (r : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) ^ ω) → ((logWidth r n : ℝ) ^ D) ≤ (n : ℝ) ^ γ := by
  let ω : ℝ := γ / (2 * ((D : ℝ) + 1))
  have hω : 0 < ω := by dsimp [ω]; positivity
  have hbudget : 2 * ω * D ≤ γ := by
    have hden : 0 < 2 * ((D : ℝ) + 1) := by positivity
    have heq : ω * (2 * ((D : ℝ) + 1)) = γ := div_mul_cancel₀ γ hden.ne'
    linarith
  have hlog := ((isLittleO_log_rpow_atTop hω).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).def (Real.log_pos (by norm_num : 1 < (2 : ℝ)))
  refine ⟨ω, hω, ?_⟩
  filter_upwards [hlog, eventually_rpow_gap (show ω < 2 * ω by linarith) 4,
    eventually_ge_atTop 1] with n hl hlarge hn
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos := zero_lt_one.trans_le hn'
  have hnω : 1 ≤ (n : ℝ) ^ ω := Real.one_le_rpow hn' hω.le
  have hl' : Real.logb 2 n ≤ (n : ℝ) ^ ω := by
    apply (div_le_iff₀ (Real.log_pos (by norm_num : 1 < (2 : ℝ)))).mpr
    simpa only [Function.comp_apply, Real.norm_of_nonneg (Real.log_nonneg hn'),
      Real.norm_of_nonneg (Real.rpow_nonneg hnpos.le ω), mul_comm] using hl
  intro r hr hrmax
  have hr' : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos := zero_lt_one.trans_le hr'
  have hrl : Real.logb 2 r ≤ (n : ℝ) ^ ω :=
    (Real.logb_le_iff_le_rpow (by norm_num : 1 < (2 : ℝ)) hrpos).mpr hrmax
  have hnn : 1 ≤ 2 * (n : ℝ) * r := by nlinarith
  have hlr := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : 1 < (2 : ℝ)) hnn)
  change (logWidth r n : ℝ) < Real.logb 2 (2 * (n : ℝ) * r) + 1 at hlr
  rw [Real.logb_mul (by positivity) hrpos.ne', Real.logb_mul (by norm_num) hnpos.ne',
    Real.logb_self_eq_one (by norm_num)] at hlr
  have hwidth : (logWidth r n : ℝ) ≤ (n : ℝ) ^ (2 * ω) := by linarith
  calc
    _ ≤ ((n : ℝ) ^ (2 * ω)) ^ D := pow_le_pow_left₀ (by positivity) hwidth D
    _ = (n : ℝ) ^ ((2 * ω) * D) := by
      rw [Real.rpow_mul hnpos.le (2 * ω) (D : ℝ), Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn' hbudget

/-- All fixed multiples of the per-processor sorting traffic eventually fit in
`n` physical inputs, for the *same* positive exponent `ω`. This includes both
the word size and the bitonic layer count in the fixed power `D`. -/
theorem eventually_sorting_links (D : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ c : ℕ, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r →
      (r : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) ^ ω) → c * block ξ n * logWidth r n ^ D ≤ n := by
  obtain ⟨ω, hω, hpoly⟩ := exists_polylog_budget D (show 0 < ξ / 6 by positivity)
  refine ⟨ω, hω, fun c => ?_⟩
  filter_upwards [hpoly, eventually_rpow_gap (show 1 - ξ / 3 + ξ / 6 < 1 by linarith) c,
    eventually_ge_atTop 1] with n hp hgap hn
  intro r hr hrmax
  have hblock := Nat.floor_le (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)) (1 - ξ / 3))
  have hlocal := mul_le_mul hblock (hp r hr hrmax) (by positivity) (by positivity)
  change (block ξ n : ℝ) * (logWidth r n : ℝ) ^ D ≤ _ at hlocal
  rw [← Real.rpow_add (by exact_mod_cast hn : 0 < (n : ℝ))] at hlocal
  rw [Real.rpow_one] at hgap
  have htotal := (mul_le_mul_of_nonneg_left hlocal (by positivity : 0 ≤ (c : ℝ))).trans hgap
  rw [← mul_assoc] at htotal
  exact_mod_cast htotal

end TeamScales

end BorderVNP
end Computability
end OAI
