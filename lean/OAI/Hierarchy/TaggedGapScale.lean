import OAI.Hierarchy.TaggedApproximation
import OAI.Hierarchy.TaggedRadixPrice
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace OAI
/-! # Logarithmic-square error budgets at tagged tree heights -/

noncomputable section
namespace Hierarchy.Tagged

open Filter Real Asymptotics

theorem gap_pos (C : ℝ) (h : ℕ) : 0 < gap C h := by unfold gap; positivity

namespace GapScale

private abbrev L (h : ℕ) : ℝ := logb 2 (2*(h:ℝ))

private theorem L_one {h : ℕ} (hh : 1 ≤ h) : 1 ≤ L h := by
  have hr : (1:ℝ) ≤ h := by exact_mod_cast hh
  calc
    (1:ℝ) = logb 2 2 := (logb_self_eq_one (by norm_num)).symm
    _ ≤ _ := logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)

private theorem L_nonneg (h : ℕ) : 0 ≤ L h := by
  rcases Nat.eq_zero_or_pos h with rfl | hp
  · simp [L]
  · linarith [L_one hp]

private theorem large_log : Tendsto L atTop atTop := by
  have times_two : Tendsto (fun h : ℕ => 2*(h:ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ)<2)).2 tendsto_natCast_atTop_atTop
  exact (tendsto_logb_atTop (by norm_num : (1:ℝ)<2)).comp times_two

private theorem exp_log {h : ℕ} (hh : 0 < h) (b : ℝ) :
    (2*(h:ℝ))^b = (2:ℝ)^(b*L h) := by
  rw [mul_comm b, Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show (2:ℝ)^L h = 2*(h:ℝ) from rpow_logb (by norm_num) (by norm_num) (by positivity)]

theorem gap_eq_rpow (C : ℝ) (h : ℕ) : gap C h =
    (2:ℝ)^((h:ℝ)-C*(logb 2 (2*(h:ℝ)))^2) := by
  rw [gap, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  congr 1
  ring

/-- A squared binary logarithm can consume any fixed positive fraction of the square root. -/
theorem eventual_log_sq_le_sqrt (C : ℝ) {e : ℝ} (he : 0 < e) :
    ∀ᶠ h : ℕ in atTop, C*(logb 2 (2*(h:ℝ)))^2 ≤ e*sqrt (h:ℝ) := by
  have small : (fun x : ℝ => (log x)^2) =o[atTop] sqrt := by
    change (fun x : ℝ => (log x)^2) =o[atTop] fun x => sqrt x
    simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using
      isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ)<1/2)
  have large : Tendsto (fun h : ℕ => 2*(h:ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ)<2)).2 tendsto_natCast_atTop_atTop
  filter_upwards [large.eventually ((small.const_mul_left (C/(log 2)^2)).def
    (show 0 < e/2 by linarith))] with h bound
  have absBound : |C/(log 2)^2*(log (2*(h:ℝ)))^2| ≤ e/2*sqrt (2*(h:ℝ)) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _)] using bound
  have two : sqrt 2 ≤ 2 := sqrt_le_self_iff.mpr (Or.inr (by norm_num))
  calc
    _ = C/(log 2)^2*(log (2*(h:ℝ)))^2 := by rw [logb,div_pow]; ring
    _ ≤ _ := (le_abs_self _).trans absBound
    _ ≤ e*sqrt (h:ℝ) := by
      rw [sqrt_mul (by norm_num : (0:ℝ)≤2)]
      nlinarith [mul_nonneg he.le (sqrt_nonneg (h:ℝ)),
        mul_le_mul_of_nonneg_right two (mul_nonneg he.le (sqrt_nonneg (h:ℝ)))]

theorem eventual_sqrt_gap (C : ℝ) {e : ℝ} (he : 0 < e) :
    ∀ᶠ h : ℕ in atTop, (2:ℝ)^h * (2:ℝ)^(-e*sqrt (h:ℝ)) ≤ gap C h := by
  filter_upwards [eventual_log_sq_le_sqrt C he] with h bound
  unfold gap
  exact mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
    (by positivity)

private theorem eventual_budget (C b : ℝ) :
    ∀ᶠ h : ℕ in atTop, C*(L h)^2 + b*L h ≤ (h:ℝ)/2 :=
  (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (Radix.eventual_log_budget C b)

/-- Every fixed polynomial in the height is eventually below the gap. -/
theorem eventual_polynomial (C A b : ℝ) (_hb : 0 ≤ b) :
    ∀ᶠ h : ℕ in atTop, A*(2*(h:ℝ))^b ≤ gap C h := by
  filter_upwards [eventual_budget C (b+1),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop A,
    eventually_ge_atTop (1:ℕ)] with h small large hh
  have pos : 0 < 2*(h:ℝ) := by positivity
  calc
    _ ≤ (2*(h:ℝ))*(2*(h:ℝ))^b :=
      mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α:=ℝ) h]) (by positivity)
    _ = (2*(h:ℝ))^(b+1) := by rw [Real.rpow_add_one pos.ne']; ring
    _ = (2:ℝ)^((b+1)*L h) := exp_log hh _
    _ ≤ gap C h := by
      rw [gap_eq_rpow]
      apply rpow_le_rpow_of_exponent_le (by norm_num)
      change _ ≤ (h:ℝ)-C*(L h)^2
      linarith [Nat.cast_nonneg (α:=ℝ) h]

/-- At heights differing by a factor of at least 3/2, the quadratic logarithms
differ by at least half the larger logarithm, including a child of height zero. -/
private theorem short_log {h t : ℕ} (hh : 1 ≤ h) (short : 3*t ≤ 2*h) :
    (L h)^2 - (L t)^2 ≥ L h/2 := by
  have big := L_one hh
  have small := L_nonneg t
  have ht : L t + 1/2 ≤ L h := by
    rcases Nat.eq_zero_or_pos t with rfl | hp
    · simpa [L] using (show (1/2:ℝ) ≤ L h by linarith)
    · have cast : 3*(t:ℝ) ≤ 2*(h:ℝ) := by exact_mod_cast short
      have shift : (1/2:ℝ) ≤ logb 2 (3/2) := by
        have aux := logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<2)
          (show (2:ℝ)≤(3/2:ℝ)^2 by norm_num)
        rw [logb_self_eq_one (by norm_num), logb_pow] at aux
        push_cast at aux
        linarith
      have le := logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
        (show 0 < (2*(t:ℝ))*(3/2) by positivity)
        (show (2*(t:ℝ))*(3/2) ≤ 2*(h:ℝ) by linarith)
      rw [logb_mul (by positivity : 2*(t:ℝ) ≠ 0) (by norm_num : (3/2:ℝ) ≠ 0)] at le
      change logb 2 (2*(t:ℝ)) + _ ≤ _
      linarith only [le,shift]
  nlinarith [mul_nonneg (by linarith : 0 ≤ L h-L t-1/2)
    (by linarith : 0 ≤ L h+L t)]

/-- The coefficient six pays the quadratic divisor and leaves a full linear
factor at the parent height. The same coefficient works for every fixed
amplification target, capacity constant and positive mass fraction. -/
theorem eventual_shorter_amplification {D a C B : ℝ} (hD : 6 ≤ D)
    (ha : 0 < a) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    ∀ᶠ h : ℕ in atTop, ∀ (t : ℕ) (s H : ℝ), 3*t ≤ 2*h →
      a*(2:ℝ)^h ≤ s*(2:ℝ)^t → 0 < H → H ≤ C*((t:ℝ)+1)^2 →
      B*gap D h ≤ s*gap D t/(2*H) := by
  filter_upwards [eventually_ge_atTop (1:ℕ),
    (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (B*C/a)] with h hh scale
  intro t s H short mass hH cap
  have hr : (1:ℝ) ≤ h := by exact_mod_cast hh
  have tr : (t:ℝ) ≤ h := by exact_mod_cast (show t ≤ h by omega)
  have lc := short_log hh short
  have weight : (2*(h:ℝ))^3*(2:ℝ)^(-D*(L h)^2) ≤ (2:ℝ)^(-D*(L t)^2) := by
    rw [← Real.rpow_natCast (2*(h:ℝ)) 3, exp_log hh, ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    apply rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left lc (show 0 ≤ D by linarith),
      mul_nonneg (sub_nonneg.mpr hD) (L_nonneg h)]
  have bound : H ≤ C*(2*(h:ℝ))^2 := by
    refine cap.trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have capprice : B*(2*H) ≤ a*(2*(h:ℝ))^3 := by
    have fit := (div_le_iff₀ ha).mp scale
    have priced := mul_le_mul_of_nonneg_left bound hB
    nlinarith only [priced,mul_le_mul_of_nonneg_right fit (sq_nonneg (2*(h:ℝ)))]
  apply (le_div_iff₀ (by positivity)).mpr
  unfold gap
  change B*((2:ℝ)^h*(2:ℝ)^(-D*(L h)^2))*(2*H) ≤ s*((2:ℝ)^t*(2:ℝ)^(-D*(L t)^2))
  calc
    _ ≤ (a*(2*(h:ℝ))^3)*((2:ℝ)^h*(2:ℝ)^(-D*(L h)^2)) := by
      convert mul_le_mul_of_nonneg_right capprice
        (show 0 ≤ (2:ℝ)^h*(2:ℝ)^(-D*(L h)^2) by positivity) using 1; ring
    _ = (a*(2:ℝ)^h)*((2*(h:ℝ))^3*(2:ℝ)^(-D*(L h)^2)) := by ring
    _ ≤ (a*(2:ℝ)^h)*(2:ℝ)^(-D*(L t)^2) := mul_le_mul_of_nonneg_left weight (by positivity)
    _ ≤ (s*(2:ℝ)^t)*(2:ℝ)^(-D*(L t)^2) := mul_le_mul_of_nonneg_right mass (by positivity)
    _ = _ := by ring

/-- The amplified gap exceeds every fixed real multiple of the parent gap. -/
theorem eventual_shorter_strict {D a C : ℝ} (hD : 6 ≤ D) (ha : 0 < a) (hC : 0 ≤ C)
    (B : ℝ) :
    ∀ᶠ h : ℕ in atTop, ∀ (t : ℕ) (s H : ℝ), 3*t ≤ 2*h →
      a*(2:ℝ)^h ≤ s*(2:ℝ)^t → 0 < H → H ≤ C*((t:ℝ)+1)^2 →
      B*gap D h < s*gap D t/(2*H) := by
  have pos : 0 ≤ max B 0+1 := by linarith [le_max_right B 0]
  filter_upwards [eventual_shorter_amplification hD ha hC pos] with h scale
  intro t s H short mass hp bound
  exact (mul_lt_mul_of_pos_right (by linarith [le_max_left B 0] : B < max B 0+1)
    (gap_pos D h)).trans_le (scale t s H short mass hp bound)

/-- At every taller height the smaller quadratic-log coefficient leaves enough
room for an arbitrary fixed polynomial in the taller height itself. -/
theorem eventual_taller_absorption {C D b : ℝ} (hC : 0 ≤ C) (hCD : C < D) (hb : 0 ≤ b) :
    ∀ᶠ h : ℕ in atTop, ∀ t : ℕ, h ≤ t → (2*(t:ℝ))^b * gap D h ≤ gap C t := by
  filter_upwards [eventually_ge_atTop (1:ℕ),
    large_log.eventually_ge_atTop ((3*C+2*b)/(D-C)),
    eventually_forall_ge_atTop.mpr (eventual_budget C b)] with h hh enough budget
  intro t ht
  have pos : 0 < t := hh.trans ht
  have hL := L_one hh
  have hr : (h:ℝ) ≤ t := by exact_mod_cast ht
  rw [exp_log pos b, gap_eq_rpow, gap_eq_rpow, ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  apply rpow_le_rpow_of_exponent_le (by norm_num)
  change b*L t+((h:ℝ)-D*(L h)^2) ≤ (t:ℝ)-C*(L t)^2
  by_cases hc : t ≤ 2*h
  · have lim : L t ≤ L h+1 := by
      have cast : (t:ℝ) ≤ 2*(h:ℝ) := by exact_mod_cast hc
      have up := logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
        (show 0<2*(t:ℝ) by positivity)
        (show 2*(t:ℝ)≤(2*(h:ℝ))*2 by linarith)
      rwa [logb_mul (by positivity : 2*(h:ℝ) ≠ 0) (by norm_num : (2:ℝ)≠0),
        logb_self_eq_one (by norm_num)] at up
    have sq : (L t)^2 ≤ (L h+1)^2 := pow_le_pow_left₀ (L_nonneg t) lim _
    have scaled := (div_le_iff₀ (sub_pos.mpr hCD)).mp enough
    nlinarith only [mul_le_mul_of_nonneg_right scaled (L_nonneg h),
      mul_le_mul_of_nonneg_left sq hC,mul_le_mul_of_nonneg_left lim hb,
      mul_nonneg (add_nonneg hC hb) (sub_nonneg.mpr hL),hr]
  · have far : 2*(h:ℝ) ≤ t := by exact_mod_cast (show 2*h ≤ t by omega)
    linarith only [budget t ht,far,mul_nonneg (hC.trans hCD.le) (sq_nonneg (L h))]

/-- The same strict coefficient margin pays a logarithmic reduction in address
height, as occurs when one wide pack replaces a polynomial number of rows. -/
theorem eventual_log_shift {C D b J : ℝ} (hC : 0 ≤ C) (hCD : C < D) (hb : 0 ≤ b) :
    ∀ᶠ h : ℕ in atTop, ∀ t : ℕ, (h:ℝ) ≤ (t:ℝ)+J*logb 2 (2*(h:ℝ)) →
      (2*(h:ℝ))^b*gap D h ≤ gap C t := by
  filter_upwards [eventual_taller_absorption hC hCD hb,
    large_log.eventually_ge_atTop ((J+b)/(D-C)),eventually_ge_atTop (1:ℕ)] with h above large hh
  intro t relative
  by_cases tall : h ≤ t
  · refine (mul_le_mul_of_nonneg_right ?_ (gap_pos D h).le).trans (above t tall)
    exact rpow_le_rpow (by positivity) (by exact_mod_cast Nat.mul_le_mul_left 2 tall) hb
  · have ht : (t:ℝ) ≤ h := by exact_mod_cast (show t ≤ h by omega)
    have less : L t ≤ L h := by
      rcases Nat.eq_zero_or_pos t with rfl | hp
      · simpa [L] using L_nonneg h
      · exact logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
    have sq := pow_le_pow_left₀ (L_nonneg t) less 2
    have fit := (div_le_iff₀ (sub_pos.mpr hCD)).mp large
    rw [exp_log hh b,gap_eq_rpow,gap_eq_rpow,← rpow_add (by norm_num : (0:ℝ)<2)]
    apply rpow_le_rpow_of_exponent_le (by norm_num)
    change b*L h+((h:ℝ)-D*(L h)^2) ≤ (t:ℝ)-C*(L t)^2
    change (h:ℝ) ≤ (t:ℝ)+J*L h at relative
    nlinarith only [relative,mul_le_mul_of_nonneg_right fit (L_nonneg h),
      mul_le_mul_of_nonneg_left sq hC]

theorem antitone_coefficient {C D : ℝ} (le : C ≤ D) (h : ℕ) : gap D h ≤ gap C h := by
  rw [gap_eq_rpow,gap_eq_rpow]
  apply rpow_le_rpow_of_exponent_le (by norm_num)
  linarith only [mul_le_mul_of_nonneg_right le (sq_nonneg (logb 2 (2*(h:ℝ))))]

/-- A coefficient gap at equal heights also leaves an arbitrary fixed
multiplicative constant in addition to any prescribed polynomial degree. -/
theorem eventual_taller_polynomial {C D b : ℝ} (hC : 0 ≤ C) (hCD : C < D)
    (hb : 0 ≤ b) (A : ℝ) :
    ∀ᶠ h : ℕ in atTop, ∀ t : ℕ, h ≤ t → A*(2*(t:ℝ))^b*gap D h ≤ gap C t := by
  filter_upwards [eventual_taller_absorption hC hCD (show 0≤b+1 by linarith),
    (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop A,
    eventually_ge_atTop (1:ℕ)] with h bound large one
  intro t ht
  have le : A ≤ 2*(t:ℝ) := by
    have hr : (h:ℝ) ≤ t := by exact_mod_cast ht
    linarith [Nat.cast_nonneg (α:=ℝ) t]
  have pos : 0 < 2*(t:ℝ) := by have htpos : 0 < t := one.trans ht; positivity
  refine (mul_le_mul_of_nonneg_right ?_ (gap_pos D h).le).trans (bound t ht)
  rw [Real.rpow_add_one pos.ne',mul_comm ((2*(t:ℝ))^b)]
  exact mul_le_mul_of_nonneg_right le (by positivity)

/-- Uniform polynomial absorption also gives the usual little-o statement for
any sequence of control calls of at least the parent height. -/
theorem isLittleO_taller {C D b : ℝ} (hC : 0 ≤ C) (hCD : C < D)
    (hb : 0 ≤ b) {t : ℕ → ℕ} (taller : ∀ᶠ h in atTop, h ≤ t h) :
    (fun h : ℕ => (2*(t h:ℝ))^b * gap D h) =o[atTop] fun h => gap C (t h) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro e he
  filter_upwards [eventual_taller_polynomial hC hCD hb (1/e),taller] with h bound ht
  have fit := bound (t h) ht
  have nonneg : 0 ≤ (2*(t h:ℝ))^b * gap D h :=
    mul_nonneg (rpow_nonneg (by positivity) _) (gap_pos D h).le
  simp only [Real.norm_eq_abs,abs_of_nonneg nonneg,abs_of_nonneg (gap_pos C (t h)).le]
  calc
    _ = e*((1/e)*(2*(t h:ℝ))^b*gap D h) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left fit he.le

/-- A positive fraction of the original row count dominates any prescribed
fixed multiple of the error budget. -/
theorem eventual_mass {D a : ℝ} (hD : 0 < D) (ha : 0 < a) (B : ℝ) :
    ∀ᶠ h : ℕ in atTop, B*gap D h ≤ a*(2:ℝ)^h := by
  filter_upwards [eventual_taller_polynomial (C:=0) le_rfl hD (b:=0) le_rfl (B/a)] with h hh
  have fit := hh h le_rfl
  simp only [Real.rpow_zero,mul_one, gap,neg_zero,zero_mul] at fit
  change B*((2:ℝ)^h*(2:ℝ)^(-D*(L h)^2)) ≤ a*(2:ℝ)^h
  calc
    _ = a*((B/a)*((2:ℝ)^h*(2:ℝ)^(-D*(L h)^2))) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left fit ha.le

/-- Polynomial height bounds on the correction interface put its logarithmic
threshold below the gap, uniformly over the possible interfaces. -/
theorem eventual_interface_threshold (D : ℝ) (k : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ h : ℕ in atTop, ∀ H : ℝ, 0 ≤ H → H ≤ C*((h:ℝ)+1)^2 →
      4*(k:ℝ)*(logb 2 H+3) ≤ gap D h := by
  filter_upwards [eventual_polynomial D (4*(k:ℝ)*(C/log 2+3)) 2 (by norm_num),
    eventually_ge_atTop (1:ℕ)] with h poly one
  intro H hH cap
  have hr : (1:ℝ) ≤ h := by exact_mod_cast one
  have full : (H:ℝ) ≤ C*(2*(h:ℝ))^2 := by
    refine cap.trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have price : logb 2 (H:ℝ) ≤ C/log 2 * (2*(h:ℝ))^2 := by
    have raw := (Real.log_le_self hH).trans full
    rw [logb,div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right raw (log_pos (by norm_num : (1:ℝ)<2)).le
  rw [Real.rpow_two] at poly
  refine le_trans ?_ poly
  have sq : (1:ℝ) ≤ (2*(h:ℝ))^2 := by
    nlinarith [sq_nonneg ((h:ℝ)-1)]
  have bound : logb 2 (H:ℝ)+3 ≤ (C/log 2+3)*(2*(h:ℝ))^2 := by linarith only [price,sq]
  convert mul_le_mul_of_nonneg_left bound (show 0 ≤ 4*(k:ℝ) by positivity) using 1; ring

end GapScale

end Hierarchy.Tagged

end
end OAI
