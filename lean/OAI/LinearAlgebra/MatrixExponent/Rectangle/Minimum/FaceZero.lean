import Mathlib.Analysis.Convex.Slope
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

section
/-! # Finite secants of a semiconvex defect along one ray -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
open Set

def Semiconvex (g : ℝ → ℝ) (C : ℝ) : Prop :=
  ConvexOn ℝ (Ici 0) (fun t => g t + C * t ^ 2)

variable {g : ℝ → ℝ} {C a t r : ℝ}

private theorem Semiconvex.slope (h : Semiconvex g C) (ha : 0 < a) (ht : a ≤ t) :
    (g a + C * a ^ 2 - g 0) / a ≤ (g t + C * t ^ 2 - g 0) / t := by
  simpa using h.secant_mono (show (0 : ℝ) ∈ Ici 0 from Set.mem_Ici.mpr le_rfl) ha.le (ha.trans_le ht).le
    ha.ne' (ha.trans_le ht).ne' ht

/-- Before subtracting the value at zero, the translated increment may
be negative. The subtracted increment is bounded below by a linear error. -/
theorem Semiconvex.shift (h : Semiconvex g C) (ha : 0 < a) (ht : 0 < t) :
    g a - g 0 - 2 * C * a * t ≤ g (t + a) - g t := by
  have h₁ := (div_le_iff₀ ha).mp (h.slope ha (le_add_of_nonneg_left ht.le))
  have h₂ := (div_le_iff₀ ht).mp (h.slope ht (le_add_of_nonneg_right ha.le))
  have he := div_mul_cancel₀ (g (t + a) + C * (t + a) ^ 2 - g 0) (add_pos ht ha).ne'
  linarith only [h₁, h₂, he]

/-- One number controls the change near zero and gives a lower bound at
all larger arguments. No derivative at zero is needed. -/
theorem Semiconvex.envelope (h : Semiconvex g C) (hC : 0 ≤ C)
    (hn : ∀ t, 0 ≤ t → 0 ≤ g t) (hr : 0 < r) :
    ∃ S : ℝ, 0 ≤ S ∧
      (∀ t, 0 < t → t ≤ 2 * r → g t - g 0 ≤ t * S) ∧
      (∀ t, 2 * r ≤ t → t * (S - g 0 / (2 * r)) - C * t ^ 2 ≤ g t) := by
  let S := (g (2 * r) + C * (2 * r) ^ 2) / (2 * r)
  have hz := hn 0 le_rfl
  have hr' : 0 < 2 * r := by positivity
  have he : (g (2 * r) + C * (2 * r) ^ 2 - g 0) / (2 * r) = S - g 0 / (2 * r) := sub_div _ _ _
  refine ⟨S, div_nonneg (add_nonneg (hn _ hr'.le) (by positivity)) hr'.le, ?_, ?_⟩
  · intro t ht ht'
    have hh := (div_le_iff₀ ht).mp (h.slope ht ht')
    rw [he] at hh
    have hz' : 0 ≤ g 0 / (2 * r) * t := by positivity
    have hCt : 0 ≤ C * t ^ 2 := by positivity
    linarith
  · intro t ht
    have hh := (le_div_iff₀ (hr'.trans_le ht)).mp (h.slope hr' ht)
    rw [he] at hh
    linarith

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
end

section
/-!
# Semiconvexity in reciprocal coordinates

Convexity and the one-sided transport bound make `D(r) + r` convex
and nondecreasing. A quadratic correction then absorbs the negative
reciprocal term left over after composition.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
open Set

/-- The difference of successive slopes has the sign of
`C * (a+x) * (a+y) * (a+z) + K`. -/
private theorem convex_quadratic_reciprocal {a C K : ℝ} (ha : 0 < a)
    (hC : 0 ≤ C) (hK : 0 ≤ C * a ^ 3 + K) :
    ConvexOn ℝ (Ici 0) (fun t => C * t ^ 2 + K / (a + t)) := by
  apply convexOn_of_slope_mono_adjacent (convex_Ici 0)
  intro x y z hx hz hxy hyz
  change 0 ≤ x at hx
  change 0 ≤ z at hz
  have hy := (hx.trans_lt hxy).le
  have h₁ := sub_pos.mpr hxy
  have h₂ := sub_pos.mpr hyz
  have h₃ := sub_pos.mpr (hxy.trans hyz)
  let P := (a + x) * (a + y) * (a + z)
  have hP : 0 < P := by unfold P; positivity
  have hP' : a ^ 3 ≤ P := by
    rw [show a ^ 3 = a * a * a by ring]
    unfold P
    gcongr <;> linarith
  have hsign : 0 ≤ C * P + K := hK.trans (by gcongr)
  apply sub_nonneg.mp
  calc
    0 ≤ (z - x) * (C * P + K) / P := by positivity
    _ = _ := by unfold P; field_simp; ring

private theorem convex_reciprocal {a : ℝ} (ha : 0 < a) :
    ConvexOn ℝ (Ici 0) (fun t => 1 / (a + t)) := by
  simpa only [zero_mul, zero_add] using
    (convex_quadratic_reciprocal (C := 0) (K := 1) ha le_rfl (by simp))

theorem reciprocal_semiconvex {D : ℝ → ℝ} (h : ConvexOn ℝ (Ioi 0) D)
    (hmono : MonotoneOn (fun r => D r + r) (Ioi 0)) {a b c C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hC : 2 / a ^ 3 ≤ C) :
    Semiconvex (fun t => D (1 / (a + t)) - 1 / (a + t) + 1 / (b + t) - c) C := by
  have hD : ConvexOn ℝ (Ioi 0) (fun r => D r + r) := h.add (convexOn_id h.1)
  have hr := convex_reciprocal ha
  have hpos {x : ℝ} (hx : x ∈ Ici 0) : 1 / (a + x) ∈ Ioi 0 :=
    one_div_pos.mpr (add_pos_of_pos_of_nonneg ha hx)
  have hf : ConvexOn ℝ (Ici 0) (fun t => D (1 / (a + t)) + 1 / (a + t)) := by
    refine ⟨hr.1, ?_⟩
    intro x hx y hy s t hs ht hst
    exact (hmono (hpos (hr.1 hx hy hs ht hst)) (hD.1 (hpos hx) (hpos hy) hs ht hst)
      (hr.2 hx hy hs ht hst)).trans (hD.2 (hpos hx) (hpos hy) hs ht hst)
  have hq := convex_quadratic_reciprocal (K := -2) ha
    ((by positivity : (0 : ℝ) ≤ 2 / a ^ 3).trans hC) (by linarith [(div_le_iff₀ (pow_pos ha 3)).mp hC])
  refine (((hf.add hq).add (convex_reciprocal hb)).add_const (-c)).congr ?_
  intro t _
  simp only [Pi.add_apply]
  ring

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
end

/-!
# Translation of a truncated directional integral

After shifting the variable the interval loses a short prefix but gains a
nonnegative tail. On the overlap, the gain in the kernel is at least
`a / t^2`. A linear lower estimate for the defect thus gives a logarithmic gain.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
open MeasureTheory Set

def price (g : ℝ → ℝ) (u T : ℝ) := ∫ t in u..T, g t / t

variable {g : ℝ → ℝ} {u T : ℝ}

theorem price_integrable (hc : ContinuousOn g (Ici 0)) (hu : 0 < u) (hT : u ≤ T) :
    IntervalIntegrable (fun t => g t / t) volume u T := by
  apply ContinuousOn.intervalIntegrable_of_Icc hT
  exact (hc.mono (fun _ ht => hu.le.trans ht.1)).div continuousOn_id
    (fun _ ht => (hu.trans_le ht.1).ne')

theorem price_nonneg (hn : ∀ t, 0 ≤ t → 0 ≤ g t) (hu : 0 ≤ u) (hT : u ≤ T) :
    0 ≤ price g u T :=
  intervalIntegral.integral_nonneg hT fun t ht => div_nonneg (hn t (hu.trans ht.1)) (hu.trans ht.1)

private theorem gain {t a v S C : ℝ} (ha : 0 < a) (ht : a < t) (hv : 0 ≤ v)
    (hS : t * S - C * t ^ 2 ≤ v) : a * (S * t⁻¹ - C) ≤ v / (t - a) - v / t := by
  have ht₀ : 0 < t := ha.trans ht
  have hta : 0 < t - a := sub_pos.mpr ht
  calc
    _ = a * (t * S - C * t ^ 2) / (t * t) := by field_simp
    _ ≤ a * v / (t * t) := by gcongr
    _ ≤ a * v / (t * (t - a)) := by gcongr; linarith
    _ = _ := by field_simp; ring

theorem integrate_gain {a S C : ℝ} (hu : 0 < u) (hT : u ≤ T) :
    (∫ t in u..T, a * (S * t⁻¹ - C)) = a * (S * Real.log (T / u) - (T - u) * C) := by
  have hi : IntervalIntegrable (fun t : ℝ => t⁻¹) volume u T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    exact continuousOn_id.inv₀ (fun _ ht => (hu.trans_le ht.1).ne')
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hi.const_mul S) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_inv_of_pos hu (hu.trans_le hT),
    intervalIntegral.integral_const, smul_eq_mul]

theorem translation (hc : ContinuousOn g (Ici 0)) (hn : ∀ t, 0 ≤ t → 0 ≤ g t)
    {a r R T B S C : ℝ} (ha : 0 < a) (hr : a ≤ r) (hR : 2 * r ≤ R) (hT : R ≤ T) (hC : 0 ≤ C)
    (hB : ∀ t, r ≤ t → t ≤ r + a → g t ≤ B * r)
    (hS : ∀ t, 2 * r ≤ t → t ≤ R → t * S - C * t ^ 2 ≤ g t) :
    a * (S * Real.log (R / (2 * r)) - C * R - B) ≤ price (fun t => g (t + a)) r T - price g r T := by
  have hr₀ := ha.trans_le hr
  have hra : r + a ≤ 2 * r := by linarith
  have hrT : r + a ≤ T := hra.trans (hR.trans hT)
  let f (t : ℝ) := g t / (t - a)
  have hf {u v : ℝ} (hu : r + a ≤ u) (hv : u ≤ v) : IntervalIntegrable f volume u v := by
    apply ContinuousOn.intervalIntegrable_of_Icc hv
    have hu₀ : 0 < u := by linarith
    exact (hc.mono (fun _ ht => hu₀.le.trans ht.1)).div
      (continuousOn_id.sub continuousOn_const) (fun t ht => by change t - a ≠ 0; linarith [ht.1])
  have hshift : price (fun t => g (t + a)) r T = ∫ t in r + a..T + a, f t := by
    rw [← intervalIntegral.integral_comp_add_right f a]
    simp only [price, f, add_sub_cancel_right]
  have htail : 0 ≤ ∫ t in T..T + a, f t := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    exact div_nonneg (hn t (by linarith [ht.1])) (by linarith [ht.1])
  have hprefix : price g r (r + a) ≤ a * B := by
    have hB₀ : 0 ≤ B := nonneg_of_mul_nonneg_left
      ((hn r hr₀.le).trans (hB r le_rfl (by linarith))) hr₀
    calc
      _ ≤ ∫ _ in r..r + a, B := by
        apply intervalIntegral.integral_mono_on (by linarith) (price_integrable hc hr₀ (by linarith))
          intervalIntegrable_const
        intro t ht
        exact (div_le_iff₀ (hr₀.trans_le ht.1)).mpr
          ((hB t ht.1 ht.2).trans (mul_le_mul_of_nonneg_left ht.1 hB₀))
      _ = _ := by simp
  let diff (t : ℝ) := f t - g t / t
  have hdiff {u v : ℝ} (hu : r + a ≤ u) (hv : u ≤ v) : IntervalIntegrable diff volume u v :=
    (hf hu hv).sub (price_integrable hc (by linarith) hv)
  have hmid : (∫ t in 2 * r..R, diff t) ≤ ∫ t in r + a..T, diff t := by
    apply intervalIntegral.integral_mono_interval hra hR hT _ (hdiff le_rfl hrT)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact sub_nonneg.mpr (div_le_div_of_nonneg_left (hn t (by linarith [ht.1]))
      (by linarith [ht.1]) (by linarith))
  have hlo : a * (S * Real.log (R / (2 * r)) - (R - 2 * r) * C) ≤ ∫ t in 2 * r..R, diff t := by
    rw [← integrate_gain (by positivity) hR]
    apply intervalIntegral.integral_mono_on hR _ (hdiff hra hR)
    · intro t ht
      exact gain ha (by linarith [ht.1]) (hn t (by linarith [ht.1])) (hS t ht.1 ht.2)
    · apply ContinuousOn.intervalIntegrable_of_Icc hR
      exact continuousOn_const.mul ((continuousOn_const.mul
        (continuousOn_id.inv₀ (fun t ht => by change t ≠ 0; linarith [ht.1]))).sub continuousOn_const)
  have hfull := hlo.trans hmid
  unfold diff at hfull
  rw [intervalIntegral.integral_sub (hf le_rfl hrT) (price_integrable hc (by positivity) hrT)]
    at hfull
  rw [hshift, ← intervalIntegral.integral_add_adjacent_intervals (hf le_rfl hrT) (hf hrT (by linarith))]
  unfold price at hprefix ⊢
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (price_integrable hc hr₀ (show r ≤ r + a by linarith)) (price_integrable hc (by positivity) hrT)]
  linarith only [hfull, htail, hprefix, show 0 ≤ a * r * C by positivity]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
end

section
/-!
# Dilation at a zero of the defect

A fixed interval of positive mass forces a strict decrease under dilation.
Continuity at zero controls the mass added below the lower cutoff.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
open MeasureTheory Set Filter

variable {g : ℝ → ℝ}

private theorem price_mono_interval (hc : ContinuousOn g (Ici 0)) (hn : ∀ t, 0 ≤ t → 0 ≤ g t)
    {u a b T : ℝ} (hu : 0 < u) (hua : u ≤ a) (hab : a ≤ b) (hbT : b ≤ T) :
    price g a b ≤ price g u T := by
  apply intervalIntegral.integral_mono_interval hua hab hbT _
    (price_integrable hc hu (hua.trans (hab.trans hbT)))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact div_nonneg (hn t (hu.trans ht.1).le) (hu.trans ht.1).le

private theorem price_dilate {q u T : ℝ} (hq : 0 < q) :
    price (fun t => g (t / q) / q) u T = price g (u / q) (T / q) / q := by
  unfold price
  calc
    _ = ∫ t in u..T, (q ^ 2)⁻¹ * (g (t / q) / (t / q)) := by
      apply intervalIntegral.integral_congr
      intro t _
      by_cases ht : t = 0
      · simp [ht]
      · field_simp
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_div (fun t => g t / t) hq.ne', smul_eq_mul]
      field_simp

theorem dilation (hc : ContinuousOn g (Ici 0)) (hn : ∀ t, 0 ≤ t → 0 ≤ g t)
    (hg : g 0 = 0) (hw : ∃ t, 0 < t ∧ 0 < g t) :
    ∃ D : ℝ, 0 < D ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ T : ℝ in atTop,
      price (fun t => g (t / (1 + ε)) / (1 + ε)) (1 / T) T - price g (1 / T) T ≤ -ε * D := by
  obtain ⟨t, ht, hgt⟩ := hw
  let C := price g t (2 * t)
  have hC : 0 < C := by
    apply intervalIntegral.integral_pos (by linarith)
    · exact (hc.mono (fun _ hs => ht.le.trans hs.1)).div continuousOn_id
        (fun _ hs => (ht.trans_le hs.1).ne')
    · exact fun s hs => div_nonneg (hn s (ht.trans hs.1).le) (ht.trans hs.1).le
    · exact ⟨t, ⟨le_rfl, by linarith⟩, div_pos hgt ht⟩
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuousWithinAt_iff.mp (hc 0 (by simp)) (C / 2) (by positivity)
  refine ⟨C / 4, by positivity, ?_⟩
  intro ε hε hε'
  let q := 1 + ε
  have hq : 0 < q := by unfold q; linarith
  have hq' : 1 ≤ q := by unfold q; linarith
  filter_upwards [eventually_ge_atTop (2 * t), eventually_gt_atTop (1 / t),
    eventually_gt_atTop (1 / δ)] with T hT hTt hTδ
  have hT₀ : 0 < T := by linarith
  let u := 1 / T
  have hu : 0 < u := by unfold u; positivity
  have hut : u ≤ t := ((one_div_lt hT₀ ht).mpr hTt).le
  have huδ : u < δ := (one_div_lt hT₀ hδ).mpr hTδ
  have huT : u ≤ T := by linarith
  have huq : 0 < u / q := div_pos hu hq
  have huq' : u / q ≤ u := div_le_self hu.le hq'
  have hmass : C ≤ price g u T := price_mono_interval hc hn hu hut (by linarith) hT
  have hprefix : price g (u / q) u ≤ ε * (C / 2) := by
    calc
      _ ≤ ∫ _ in u / q..u, (C / 2) / (u / q) := by
        apply intervalIntegral.integral_mono_on huq' (price_integrable hc huq huq')
          intervalIntegrable_const
        intro s hs
        have hs₀ := huq.trans_le hs.1
        have hd := hsmall hs₀.le (by simpa [Real.dist_eq, abs_of_pos hs₀] using hs.2.trans_lt huδ)
        have hg' : g s ≤ C / 2 := by simpa [hg, Real.dist_eq, abs_of_nonneg (hn s hs₀.le)] using hd.le
        exact div_le_div₀ (by positivity) hg' huq hs.1
      _ = _ := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        field_simp
        unfold q
        ring
  have hbound : price g (u / q) (T / q) ≤ ε * (C / 2) + price g u T := calc
    _ ≤ price g (u / q) T := price_mono_interval hc hn huq le_rfl
      (div_le_div_of_nonneg_right huT hq.le) (div_le_self hT₀.le hq')
    _ = price g (u / q) u + price g u T :=
      (intervalIntegral.integral_add_adjacent_intervals
        (price_integrable hc huq huq') (price_integrable hc hu huT)).symm
    _ ≤ _ := add_le_add_left hprefix _
  change price (fun s => g (s / q) / q) u T - price g u T ≤ _
  rw [price_dilate hq, sub_le_iff_le_add, div_le_iff₀ hq]
  apply hbound.trans
  unfold q
  linarith only [mul_le_mul_of_nonneg_left hmass hε.le,
    mul_le_mul_of_nonneg_left hε' (mul_nonneg hε.le hC.le)]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
end

section
/-! # The cost of translating a single coordinate -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
open Set MeasureTheory

variable {g : ℝ → ℝ} {C a u r R T : ℝ}

private theorem continuous_shift (hc : ContinuousOn g (Ici 0)) (ha : 0 ≤ a) :
    ContinuousOn (fun t => g (t + a)) (Ici 0) :=
  hc.comp (continuousOn_id.add continuousOn_const) (fun _ ht => add_nonneg ht ha)

private theorem small_increment (hc : ContinuousOn g (Ici 0)) (h : Semiconvex g C)
    (ha : 0 < a) (hu : 0 < u) (hr : u ≤ r) :
    (g a - g 0) * Real.log (r / u) - (r - u) * (2 * C * a) ≤
      price (fun t => g (t + a)) u r - price g u r := by
  have he := integrate_gain (a := 1) (S := g a - g 0) (C := 2 * C * a) hu hr
  simp only [one_mul] at he
  rw [← he, price, price, ← intervalIntegral.integral_sub
    (price_integrable (continuous_shift hc ha.le) hu hr) (price_integrable hc hu hr)]
  apply intervalIntegral.integral_mono_on hr
  · apply ContinuousOn.intervalIntegrable_of_Icc hr
    exact (continuousOn_const.mul (continuousOn_id.inv₀
      (fun _ ht => (hu.trans_le ht.1).ne'))).sub continuousOn_const
  · exact (price_integrable (continuous_shift hc ha.le) hu hr).sub (price_integrable hc hu hr)
  intro t ht
  have ht₀ := hu.trans_le ht.1
  rw [← sub_div, le_div_iff₀ ht₀, sub_mul, mul_assoc, inv_mul_cancel₀ ht₀.ne', mul_one]
  exact h.shift ha ht₀

/-- The logarithmic gain at intermediate distances pays for the possible
increase in the defect when the path switches coordinates. -/
theorem increment (hc : ContinuousOn g (Ici 0)) (hn : ∀ t, 0 ≤ t → 0 ≤ g t)
    (h : Semiconvex g C) (hC : 0 ≤ C) {L : ℝ} (hL : 2 ≤ L)
    (ha : 0 < a) (har : a * (L + 2) ≤ r) (hR : 2 * r ≤ R)
    (he : Real.log (R / (2 * r)) = L) (hu : 0 < u) (hur : u ≤ r) (hT : R ≤ T) :
    (g a - g 0) * Real.log (r / u) + (L - 2) * max (g a - g 0) 0 - g 0 - 2 * C * a * R ≤
      price (fun t => g (t + a)) u T - price g u T := by
  have hr : 0 < r := hu.trans_le hur
  have ha' : a ≤ r := (le_mul_of_one_le_right ha.le (by linarith)).trans har
  have hrT : r ≤ T := by linarith
  have hz := hn 0 le_rfl
  obtain ⟨S, hS, hl, hh⟩ := h.envelope hC hn hr
  have hb : ∀ t, r ≤ t → t ≤ r + a → g t ≤ (g 0 / r + 2 * S) * r := by
    intro t ht ht'
    have ht'' : t ≤ 2 * r := by linarith
    rw [add_mul, div_mul_cancel₀ _ hr.ne']
    linarith [hl t (hr.trans_le ht) ht'', mul_le_mul_of_nonneg_right ht'' hS]
  have hlarge := translation hc hn ha ha' hR hT hC hb (fun t ht _ => hh t ht)
  rw [he] at hlarge
  have hsmall := small_increment hc h ha hu hur
  have hgain : (L - 2) * max (g a - g 0) 0 ≤ (L - 2) * (a * S) :=
    mul_le_mul_of_nonneg_left (max_le (hl a ha (by linarith)) (by positivity)) (by linarith)
  have hcost : a * (L * (g 0 / (2 * r)) + g 0 / r) ≤ g 0 := by
    calc
      _ = (a * (L + 2)) * (g 0 / (2 * r)) := by ring
      _ ≤ r * (g 0 / (2 * r)) := mul_le_mul_of_nonneg_right har (by positivity)
      _ = g 0 / 2 := by field_simp
      _ ≤ _ := by linarith
  have hcut : (r - u) * (2 * C * a) ≤ C * a * R := by
    linarith [mul_le_mul_of_nonneg_left (by linarith : 2 * (r - u) ≤ R) (mul_nonneg hC ha.le)]
  have join {g : ℝ → ℝ} (hg : ContinuousOn g (Ici 0)) :
      price g u r + price g r T = price g u T :=
    intervalIntegral.integral_add_adjacent_intervals (price_integrable hg hu hur)
      (price_integrable hg hr hrT)
  rw [← join hc, ← join (continuous_shift hc ha.le)]
  linarith only [hlarge, hsmall, hgain, hcost, hcut]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
end

/-!
# Coordinate rays and radial paths in the positive orthant

Only *differences* of truncated directional integrals are needed.
Thus the common singular subtraction in the directional identity
cancels, even when the defect is positive at an intermediate point.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
open Filter Set

abbrev Vec := Fin 3 → ℝ

def Positive (v : Vec) : Prop := ∀ i, 0 < v i

def move (v : Vec) (i : Fin 3) (t : ℝ) : Vec := Function.update v i (v i + t)

def ray (D : Vec → ℝ) (v : Vec) (i : Fin 3) (t : ℝ) : ℝ := D (move v i t)

def J (D : Vec → ℝ) (v : Vec) (i : Fin 3) (T : ℝ) : ℝ := price (ray D v i) (1 / T) T

structure Regular (D : Vec → ℝ) : Prop where
  nonneg : ∀ v, Positive v → 0 ≤ D v
  homogeneous : ∀ v, Positive v → ∀ s : ℝ, 0 < s → D (s • v) = D v / s
  continuous : ∀ v, Positive v → ∀ i, ContinuousOn (ray D v i) (Ici 0)
  convex : ∀ v, Positive v → ∃ C : ℝ, 0 ≤ C ∧
    ∀ w ∈ Icc v ((2 : ℝ) • v), ∀ i, Semiconvex (ray D w i) C

/-- The local directional comparison, in truncated form. -/
def Comparison (D : Vec → ℝ) : Prop :=
  ∀ v, Positive v → ∃ E : ℝ, 0 ≤ E ∧ ∀ w ∈ Icc v ((2 : ℝ) • v), ∀ i j,
    ∀ ζ : ℝ, 0 < ζ → ∀ᶠ T : ℝ in atTop, J D w i T - J D w j T ≤ E * D w + ζ

variable {D : Vec → ℝ} {v w : Vec} {ε s t : ℝ}

theorem Positive.move (h : Positive v) (i : Fin 3) (ht : 0 ≤ t) : Positive (move v i t) := by
  intro j
  by_cases h' : j = i
  · subst j
    simpa [Minimum.move] using add_pos_of_pos_of_nonneg (h i) ht
  · simpa [Minimum.move, h'] using h j

@[simp] theorem ray_zero (D : Vec → ℝ) (v : Vec) (i : Fin 3) : ray D v i 0 = D v := by
  simp [ray, move]

theorem ray_move (D : Vec → ℝ) (v : Vec) (i : Fin 3) (s : ℝ) :
    ray D (move v i s) i = fun t => ray D v i (t + s) := by
  funext t
  unfold ray move
  simp [add_comm, add_left_comm]

theorem Regular.scale (h : Regular D) (hv : Positive v) (i : Fin 3) (hs : 0 < s)
    (ht : 0 ≤ t) : ray D (s • v) i t = ray D v i (t / s) / s := by
  have he : move (s • v) i t = s • move v i (t / s) := by
    funext j
    by_cases h' : j = i
    · subst j; simp [move, mul_add, mul_div_cancel₀ t hs.ne']
    · simp [move, h']
  rw [ray, he, h.homogeneous _ (hv.move i (div_nonneg ht hs.le)) _ hs]
  rfl

/-- First enlarge coordinate 0, then 1, then 2. -/
def path (v : Vec) (ε : ℝ) (n : ℕ) (i : Fin 3) : ℝ :=
  if i.val < n then (1 + ε) * v i else v i

@[simp] theorem path_zero (v : Vec) (ε : ℝ) : path v ε 0 = v := by
  funext i; simp [path]

@[simp] theorem path_three (v : Vec) (ε : ℝ) : path v ε 3 = (1 + ε) • v := by
  funext i; simp [path, i.isLt]

theorem path_mem (hv : Positive v) (he : 0 ≤ ε) (he' : ε ≤ 1) (n : ℕ) :
    path v ε n ∈ Icc v ((2 : ℝ) • v) := by
  constructor <;> intro i <;> simp only [path, Pi.smul_apply, smul_eq_mul]
  all_goals split_ifs <;> nlinarith [hv i]

theorem path_succ (v : Vec) (ε : ℝ) (i : Fin 3) :
    path v ε (i.val + 1) = move (path v ε i.val) i (ε * v i) := by
  funext j
  by_cases h : j = i
  · subst j; simp [path, move, add_mul]
  · have he : j.val < i.val + 1 ↔ j.val < i.val := by omega
    simp only [move, Function.update_of_ne h, path, he]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
end

section
/-! # Passing a directional comparison to a limiting face -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
open Set Filter MeasureTheory
open scoped Topology

private theorem tail_bound {g : ℝ → ℝ} (hc : ContinuousOn g (Ici 0))
    (hg : ∀ t, 0 < t → g t ≤ 1 / t) {B T : ℝ} (hB : 0 < B) (hT : B ≤ T) :
    price g B T ≤ 1 / B := by
  have hi : IntervalIntegrable (fun t : ℝ => 1 / t ^ 2) volume B T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    exact continuousOn_const.div (continuousOn_id.pow 2) (fun _ ht => pow_ne_zero _ (hB.trans_le ht.1).ne')
  have hd (t : ℝ) (ht : t ∈ uIcc B T) : HasDerivAt (fun t : ℝ => -1 / t) (1 / t ^ 2) t := by
    rw [uIcc_of_le hT] at ht
    simpa only [id_eq, zero_mul, zero_sub, mul_one, neg_neg] using!
      (hasDerivAt_const t (-1 : ℝ)).div (hasDerivAt_id t) (hB.trans_le ht.1).ne'
  calc
    _ ≤ ∫ t in B..T, 1 / t ^ 2 := by
      apply intervalIntegral.integral_mono_on hT (price_integrable hc hB hT) hi
      intro t ht
      rw [pow_two, ← div_div]
      exact div_le_div_of_nonneg_right (hg t (hB.trans_le ht.1)) (hB.trans_le ht.1).le
    _ = -1 / T - -1 / B := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
    _ ≤ _ := by rw [neg_div, neg_div]; linarith [one_div_pos.mpr (hB.trans_le hT)]

theorem middle_bound {f g : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) (hg : ContinuousOn g (Ici 0))
    (hn : ∀ t, 0 ≤ t → 0 ≤ f t) {C B T : ℝ} (hC : 0 ≤ C) (hB : 2 ≤ B) (hT : B ≤ T)
    (hnear : ∀ t, 0 < t → -(C * t) ≤ f t - g t)
    (hfar : ∀ t, 0 < t → g t ≤ 1 / t)
    : price f (1 / B) B - price g (1 / B) B ≤
        price f (1 / T) T - price g (1 / T) T + (C + 1) / B := by
  have hB₀ : 0 < B := by linarith
  have hT₀ : 0 < T := hB₀.trans_le hT
  have hu : 0 < 1 / T := by positivity
  have ha : 0 < 1 / B := by positivity
  have hua := one_div_le_one_div_of_le hB₀ hT
  have ha₁ : 1 / B ≤ 1 := div_le_self zero_le_one (by linarith)
  have haB : 1 / B ≤ B := by linarith
  have hsmall : -(C / B) ≤ price f (1 / T) (1 / B) - price g (1 / T) (1 / B) := by
    have h₁ := price_integrable hf hu hua
    have h₂ := price_integrable hg hu hua
    unfold price
    rw [← intervalIntegral.integral_sub h₁ h₂]
    calc
      _ ≤ ∫ _ in 1 / T..1 / B, -C := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        simp only [div_eq_mul_inv]
        linarith [mul_nonneg (inv_nonneg.mpr hT₀.le) hC]
      _ ≤ _ := by
        apply intervalIntegral.integral_mono_on hua intervalIntegrable_const (h₁.sub h₂)
        intro t ht
        rw [← sub_div, le_div_iff₀ (hu.trans_le ht.1), neg_mul]
        exact hnear t (hu.trans_le ht.1)
  have hsplit (k : ℝ → ℝ) (hk : ContinuousOn k (Ici 0)) :
      price k (1 / T) T = price k (1 / T) (1 / B) + price k (1 / B) B + price k B T := by
    unfold price
    rw [intervalIntegral.integral_add_adjacent_intervals (price_integrable hk hu hua)
        (price_integrable hk ha haB),
      intervalIntegral.integral_add_adjacent_intervals (price_integrable hk hu (hua.trans haB))
        (price_integrable hk hB₀ hT)]
  rw [hsplit f hf, hsplit g hg, add_div]
  linarith only [hsmall, price_nonneg hn hB₀.le hT, tail_bound hg hfar hB₀ hT]

theorem compact_price {G : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {A B : ℝ} (hA : 0 < A) (hB : A ≤ B)
    (hc : ∀ r ∈ Ioc (0 : ℝ) 1, ContinuousOn (g r) (Ici 0))
    (hb : ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t, 0 < t → 0 ≤ g r t ∧ g r t ≤ 1 / t)
    (hl : ∀ t, 0 < t → Tendsto (fun r => g r t) (𝓝[>] 0) (𝓝 (G t))) :
    Tendsto (fun r => price (g r) A B) (𝓝[>] 0) (𝓝 (price G A B)) := by
  have he : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioc 0 1 := Ioc_mem_nhdsGT zero_lt_one
  unfold price
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1 / A / A)
  · filter_upwards [he] with r hr
    exact (intervalIntegrable_iff.mp (price_integrable (hc r hr) hA hB)).aestronglyMeasurable
  · filter_upwards [he] with r hr
    filter_upwards [] with t ht
    rw [uIoc_of_le hB] at ht
    have ht' := hA.trans ht.1
    obtain ⟨hl, hu⟩ := hb r hr t ht'
    rw [Real.norm_of_nonneg (div_nonneg hl ht'.le)]
    exact div_le_div₀ (by positivity) (hu.trans (one_div_le_one_div_of_le hA ht.1.le)) hA ht.1.le
  · exact intervalIntegrable_const
  · filter_upwards [] with t ht
    rw [uIoc_of_le hB] at ht
    exact (hl t (hA.trans ht.1)).div_const t

/-- A common estimate near zero and an inverse-square tail let the
limiting comparison pass to a reciprocal face. -/
theorem compare_limit {f g : ℝ → ℝ → ℝ} {F G A : ℝ → ℝ} {C E : ℝ} (hC : 0 ≤ C)
    (hc : ∀ r ∈ Ioc (0 : ℝ) 1, ContinuousOn (f r) (Ici 0) ∧ ContinuousOn (g r) (Ici 0))
    (hf : ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t, 0 ≤ t → 0 ≤ f r t ∧ 0 ≤ g r t)
    (hu : ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t, 0 < t → f r t ≤ 1 / t ∧ g r t ≤ 1 / t)
    (hnear : ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t, 0 < t → -(C * t) ≤ f r t - g r t)
    (hl : ∀ t, 0 < t → Tendsto (fun r => f r t) (𝓝[>] 0) (𝓝 (F t)) ∧
      Tendsto (fun r => g r t) (𝓝[>] 0) (𝓝 (G t)))
    (hA : Tendsto A (𝓝[>] 0) (𝓝 E))
    (he : ∀ r ∈ Ioc (0 : ℝ) 1, ∀ ζ : ℝ, 0 < ζ → ∀ᶠ T : ℝ in atTop,
      price (f r) (1 / T) T - price (g r) (1 / T) T ≤ A r + ζ)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∀ᶠ B : ℝ in atTop, price F (1 / B) B - price G (1 / B) B ≤ E + ζ := by
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop ((C + 1) / (ζ / 2))] with B hB hB'
  have hB₀ : 0 < B := by linarith
  have hb : 1 / B ≤ B := (div_le_self zero_le_one (by linarith)).trans (by linarith)
  have hk : (C + 1) / B ≤ ζ / 2 := (div_le_iff₀ hB₀).2 (by
    linarith [(div_le_iff₀ (half_pos hζ)).mp hB'])
  have h₁ := compact_price (one_div_pos.mpr hB₀) hb (fun r hr => (hc r hr).1)
    (fun r hr t ht => ⟨(hf r hr t ht.le).1, (hu r hr t ht).1⟩) (fun t ht => (hl t ht).1)
  have h₂ := compact_price (one_div_pos.mpr hB₀) hb (fun r hr => (hc r hr).2)
    (fun r hr t ht => ⟨(hf r hr t ht.le).2, (hu r hr t ht).2⟩) (fun t ht => (hl t ht).2)
  apply le_of_tendsto_of_tendsto (h₁.sub h₂) (hA.add_const ζ)
  filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with r hr
  obtain ⟨T, hT, ht⟩ := ((eventually_ge_atTop B).and (he r hr _ (half_pos hζ))).exists
  have hh := middle_bound (hc r hr).1 (hc r hr).2 (fun t h => (hf r hr t h).1)
    hC hB hT (hnear r hr) (fun t h => (hu r hr t h).2)
  linarith only [ht, hh, hk]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
end

section
/-!
# From a vanishing face to an interior zero

Compare the normal and tangential ray integrals on the same truncated
interval. Near zero their difference is bounded below by transport.
At infinity the tangential kernel has an integrable inverse-square bound.
On any fixed interval away from zero its integral vanishes in the face limit.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
open Set Filter MeasureTheory
open scoped Topology

variable {D : Vec → ℝ}

private theorem balance {f g : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) (hg : ContinuousOn g (Ici 0))
    (hn : ∀ t, 0 ≤ t → 0 ≤ f t) {C m B T : ℝ} (hC : 0 ≤ C) (hB : 2 ≤ B) (hT : B ≤ T)
    (hnear : ∀ t, 0 < t → -(C * t) ≤ f t - g t)
    (hfar : ∀ t, 0 < t → g t ≤ 1 / t)
    (hm : ∀ t ∈ Icc (1 : ℝ) 2, m ≤ f t / t) :
    m ≤ price f (1 / T) T - price g (1 / T) T + C / B + price g (1 / B) B + 1 / B := by
  have hB₀ : 0 < B := by linarith
  have ha : 0 < 1 / B := by positivity
  have ha₁ : 1 / B ≤ 1 := div_le_self zero_le_one (by linarith)
  have haB : 1 / B ≤ B := by linarith
  have hmid : m ≤ price f (1 / B) B := calc
    _ = ∫ _ in (1 : ℝ)..2, m := by norm_num
    _ ≤ price f 1 2 := intervalIntegral.integral_mono_on (by norm_num)
      intervalIntegrable_const (price_integrable hf (by norm_num) (by norm_num)) hm
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_interval ha₁ (by norm_num) hB _ (price_integrable hf ha haB)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact div_nonneg (hn t (ha.trans ht.1).le) (ha.trans ht.1).le
  have he := middle_bound hf hg hn hC hB hT hnear hfar
  rw [add_div] at he
  linarith only [hmid, he]

private theorem compact_limit {g : ℝ → ℝ → ℝ} {A B : ℝ} (hA : 0 < A) (hB : A ≤ B)
    (hc : ∀ r ∈ Ioc (0 : ℝ) 1, ContinuousOn (g r) (Ici 0))
    (hb : ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t, 0 < t → 0 ≤ g r t ∧ g r t ≤ 1 / t)
    (hl : ∀ t, 0 < t → Tendsto (fun r => g r t) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r => price (g r) A B) (𝓝[>] 0) (𝓝 0) := by
  simpa [price] using compact_price (G := fun _ => 0) hA hB hc hb hl

/-- A vanishing face and a uniform directional comparison up to that
face give a zero at a finite positive triple. -/
theorem face_zero (h : Regular D) {C E : ℝ} (hc : 0 ≤ C)
    (hlim : ∀ y : ℝ, 0 < y → Tendsto (fun r : ℝ => D ![r, y, 1]) (𝓝[>] 0) (𝓝 0))
    (hl : ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t : ℝ, 0 ≤ t → D ![r, 1, 1] ≤ D ![r + t, 1, 1] + C * t)
    (hu : ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t : ℝ, 0 ≤ t → D ![r, 1 + t, 1] ≤ D ![r, 1, 1] + C * t)
    (ht : ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t : ℝ, 0 < t → D ![r, 1 + t, 1] ≤ 1 / t)
    (he : ∀ r ∈ Ioc (0 : ℝ) 1, ∀ ζ : ℝ, 0 < ζ → ∀ᶠ T : ℝ in atTop,
      J D ![r, 1, 1] 0 T - J D ![r, 1, 1] 1 T ≤ E * D ![r, 1, 1] + ζ) :
    ∃ v, Positive v ∧ D v = 0 := by
  by_contra! hn
  let v (r : ℝ) : Vec := ![r, 1, 1]
  let f r := ray D (v r) 0
  let g r := ray D (v r) 1
  have hv {r} (hr : 0 < r) : Positive (v r) := by
    intro i
    fin_cases i <;> simp [v, hr]
  have hf (r t) : f r t = D ![r + t, 1, 1] := by
    unfold f ray
    congr 1
    funext i
    fin_cases i <;> simp [move, v]
  have hg (r t) : g r t = D ![r, 1 + t, 1] := by
    unfold g ray
    congr 1
    funext i
    fin_cases i <;> simp [move, v]
  have hp {r} (hr : 0 < r) (i : Fin 3) {t} (ht : 0 ≤ t) : 0 < ray D (v r) i t := by
    have h' := (hv hr).move i ht
    exact (h.nonneg _ h').lt_of_ne' (hn _ h')
  -- Without an interior zero the normal integral has a uniform positive mass.
  have hf' : ContinuousOn (f 1) (Icc 0 2) :=
    (h.continuous _ (hv zero_lt_one) _).mono Icc_subset_Ici_self
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by norm_num)) hf'
  let m := f 1 a / 2
  have hm : 0 < m := half_pos (hp zero_lt_one 0 ha.1)
  have hmass {r} (hr : r ∈ Ioc (0 : ℝ) 1) {t} (ht : t ∈ Icc (1 : ℝ) 2) : m ≤ f r t / t := by
    have hd := hmin (show r + t - 1 ∈ Icc (0 : ℝ) 2 by constructor <;> linarith [hr.1, hr.2, ht.1, ht.2])
    have hEq : f 1 (r + t - 1) = f r t := by rw [hf, hf, show 1 + (r + t - 1) = r + t by ring]
    change f 1 a ≤ f 1 (r + t - 1) at hd
    rw [hEq] at hd
    exact div_le_div₀ (hp hr.1 0 (by linarith [ht.1])).le hd (by linarith [ht.1]) ht.2
  have hnear {r} (hr : r ∈ Ioc (0 : ℝ) 1) (t) (ht : 0 < t) : -(2 * C * t) ≤ f r t - g r t := by
    rw [hf, hg]
    linarith only [hl r hr t ht.le, hu r hr t ht.le]
  have hfar {r} (hr : r ∈ Ioc (0 : ℝ) 1) (t) (ht' : 0 < t) : g r t ≤ 1 / t := by
    rw [hg]
    exact ht r hr t ht'
  have hcont (r) (hr : r ∈ Ioc (0 : ℝ) 1) : ContinuousOn (g r) (Ici 0) := h.continuous _ (hv hr.1) _
  have hzero (t) (ht' : 0 < t) : Tendsto (fun r => g r t) (𝓝[>] 0) (𝓝 0) := by
    simp only [hg]
    exact hlim _ (by linarith)
  -- Keep the middle interval fixed while approaching the face.
  have hbound (B : ℝ) (hB : 2 ≤ B) : m ≤ (2 * C + 2) / B := by
    have hB' : 0 < B := by linarith
    have hcut : 1 / B ≤ B := (div_le_self zero_le_one (by linarith)).trans (by linarith)
    have hmiddle := compact_limit (by positivity : 0 < 1 / B) hcut hcont
      (fun r hr t ht => ⟨(hp hr.1 1 ht.le).le, hfar hr t ht⟩) hzero
    have hrate := (((hlim 1 zero_lt_one).const_mul E).add hmiddle).add_const ((2 * C + 2) / B)
    simp only [mul_zero, zero_add] at hrate
    apply ge_of_tendsto hrate
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
    obtain ⟨T, hT, he'⟩ := ((eventually_ge_atTop B).and (he r hr (1 / B) (by positivity))).exists
    change price (f r) (1 / T) T - price (g r) (1 / T) T ≤ _ at he'
    have hh := balance (h.continuous _ (hv hr.1) 0) (hcont r hr)
      (fun _ ht => (hp hr.1 0 ht).le) (by positivity) hB hT (hnear hr) (hfar hr)
      (fun _ ht => hmass hr ht)
    change m ≤ price (f r) (1 / T) T - price (g r) (1 / T) T + 2 * C / B + price (g r) (1 / B) B + 1 / B at hh
    simp only [div_eq_mul_inv] at hh he' ⊢
    linarith only [hh, he']
  have ht' : Tendsto (fun B : ℝ => (2 * C + 2) / B) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  exact hm.not_ge (ge_of_tendsto ht' ((eventually_ge_atTop 2).mono hbound))

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
end

section
/-!
# From directional potentials to price comparison

The derivative along a ray from an axis gives the defect. Inverting the
ray parameter converts the derivative to the kernel of the truncated
integral. Differences of the primitives have limits at both endpoints.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
open Set Filter
open scoped Topology

/-- The comparison of axis limits is locally uniform in the
sense that one constant works throughout the positive box. -/
def HasPotential (D : Vec → ℝ) : Prop :=
  ∀ v, Positive v → ∃ E : ℝ, 0 ≤ E ∧ ∀ w ∈ Icc v ((2 : ℝ) • v),
    ∃ (G : Fin 3 → ℝ → ℝ) (b : Fin 3 → ℝ),
      (∀ i t, 0 < t → HasDerivAt (G i) (-D (move (t • w) i 1)) t) ∧
      (∀ i, Tendsto (fun T : ℝ => G i (1 / T)) atTop (𝓝 (b i))) ∧
      (∀ i j, Tendsto (fun T : ℝ => G i T - G j T) atTop (𝓝 0)) ∧
      (∀ i j, b i - b j ≤ E * D w)

variable {D : Vec → ℝ}

theorem integral_potential (h : Regular D) {w : Vec} (hw : Positive w)
    {i : Fin 3} {G : ℝ → ℝ} (hg : ∀ t : ℝ, 0 < t → HasDerivAt G (-D (move (t • w) i 1)) t)
    {T : ℝ} (hT : 1 ≤ T) : J D w i T = G (1 / T) - G T := by
  have hT₀ : 0 < T := zero_lt_one.trans_le hT
  have hu : 0 < 1 / T := by positivity
  have huT : 1 / T ≤ T := (div_le_self zero_le_one hT).trans hT
  have hd (t : ℝ) (ht : t ∈ uIcc (1 / T) T) :
      HasDerivAt (fun t => G (1 / t)) (ray D w i t / t) t := by
    rw [uIcc_of_le huT] at ht
    have ht₀ : 0 < t := hu.trans_le ht.1
    have hi : HasDerivAt (fun t : ℝ => 1 / t) (-1 / t ^ 2) t := by
      simpa only [id_eq, zero_mul, zero_sub, one_mul] using!
        (hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht₀.ne'
    have he : -D (move ((1 / t) • w) i 1) * (-1 / t ^ 2) = ray D w i t / t := by
      change -ray D ((1 / t) • w) i 1 * (-1 / t ^ 2) = _
      rw [h.scale hw i (by positivity) zero_le_one, one_div_one_div]
      field_simp
    rw [← he]
    exact (hg _ (by positivity)).comp t hi
  simpa only [J, price, one_div_one_div] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (price_integrable (h.continuous _ hw i) hu huT)

theorem comparison_of_potential (h : Regular D) (hg : HasPotential D) : Comparison D := by
  intro v hv
  obtain ⟨E, hE, hG⟩ := hg v hv
  refine ⟨E, hE, fun w hw i j ζ hζ => ?_⟩
  obtain ⟨G, b, hd, hb, hinf, he⟩ := hG w hw
  have hp : Positive w := fun k => (hv k).trans_le (hw.1 k)
  have ht := ((hb i).sub (hb j)).sub (hinf i j)
  rw [sub_zero] at ht
  have hlt := (he i j).trans_lt (lt_add_of_pos_right _ hζ)
  filter_upwards [eventually_ge_atTop (1 : ℝ), ht.eventually_lt_const hlt] with T hT ht'
  rw [integral_potential h hp (hd i) hT, integral_potential h hp (hd j) hT]
  linarith

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
end

section
/-! # Comparing a radial dilation with three coordinate increments -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
open Set Filter

variable {D : Vec → ℝ} {v : Vec} {ε r R C E ζ : ℝ}

theorem telescope (hg : Regular D) (hv : Positive v) (hz : D v = 0)
    (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hc : ∀ w ∈ Icc v ((2 : ℝ) • v), ∀ i, Semiconvex (ray D w i) C)
    (he : ∀ w ∈ Icc v ((2 : ℝ) • v), ∀ i j,
      ∀ᶠ T : ℝ in atTop, J D w i T - J D w j T ≤ E * D w + ζ)
    (hε : 0 < ε) (hε' : ε ≤ 1) (hr : 0 < r) (hR : 2 * r ≤ R)
    (hlog : Real.log (R / (2 * r)) = 2 * E + 4) (hstep : ∀ i, ε * v i * (2 * E + 6) ≤ r)
    (k : Fin 3) :
    ∀ᶠ T in atTop, -2 * C * ε * (v 0 + v 1 + v 2) * R - 4 * ζ ≤
      J D ((1 + ε) • v) k T - J D v k T := by
  let w := path v ε
  have hw (n : ℕ) : w n ∈ Icc v ((2 : ℝ) • v) := path_mem hv hε.le hε' n
  have hp (n : ℕ) : Positive (w n) := fun i => (hv i).trans_le ((hw n).1 i)
  have h₀ : D (w 0) = 0 := by simp [w, hz]
  have h₃ : D (w 3) = 0 := by
    rw [show w 3 = _ from path_three _ _, hg.homogeneous v hv _ (by positivity), hz, zero_div]
  filter_upwards [eventually_ge_atTop R, eventually_ge_atTop (1 / r),
    he _ (hw 0) k 0, he _ (hw 1) 0 1, he _ (hw 2) 1 2, he _ (hw 3) 2 k]
    with T hT hT' e₀ e₁ e₂ e₃
  have hu : 0 < 1 / T := one_div_pos.mpr ((one_div_pos.mpr hr).trans_le hT')
  have hur : 1 / T ≤ r := by
    simpa using one_div_le_one_div_of_le (one_div_pos.mpr hr) hT'
  let l := Real.log (r / (1 / T))
  have step (i : Fin 3) :
      (D (w (i.val + 1)) - D (w i.val)) * l +
        (2 * E + 2) * max (D (w (i.val + 1)) - D (w i.val)) 0 - D (w i.val) -
        2 * C * (ε * v i) * R ≤ J D (w (i.val + 1)) i T - J D (w i.val) i T := by
    let f := ray D (w i.val) i
    have hf₀ : ∀ t, 0 ≤ t → 0 ≤ f t := fun t ht => hg.nonneg _ ((hp _).move i ht)
    have heq : w (i.val + 1) = move (w i.val) i (ε * v i) := path_succ v ε i
    have hs := increment (hg.continuous _ (hp i.val) i) hf₀ (hc _ (hw _) i) hC
      (by linarith : 2 ≤ 2 * E + 4) (mul_pos hε (hv i)) (by linarith [hstep i]) hR hlog hu hur hT
    rw [ray_zero, ← ray_move, ← heq, show 2 * E + 4 - 2 = 2 * E + 2 by ring] at hs
    simpa only [J, ray, ← heq] using hs
  have s₀ := step 0
  have s₁ := step 1
  have s₂ := step 2
  simp only [Fin.val_zero, Fin.val_one, show (2 : Fin 3).val = 2 from rfl, Nat.reduceAdd, h₀, h₃,
    sub_zero, zero_sub] at s₀ s₁ s₂
  have hm :
      D (w 1) + D (w 2) ≤
        2 * (max (D (w 1)) 0 + max (D (w 2) - D (w 1)) 0 + max (-D (w 2)) 0) := by
    linarith only [le_max_left (D (w 1)) 0, le_max_left (D (w 2) - D (w 1)) 0,
      le_max_right (D (w 2) - D (w 1)) 0, le_max_right (-D (w 2)) 0]
  have hm' := mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ E + 1)
  rw [h₀] at e₀
  rw [h₃] at e₃
  have hres : -2 * C * ε * (v 0 + v 1 + v 2) * R - 4 * ζ ≤ J D (w 3) k T - J D (w 0) k T := by
    linarith only [s₀, s₁, s₂, e₀, e₁, e₂, e₃, hm']
  simpa only [w, path_zero, path_three] using hres

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
end
