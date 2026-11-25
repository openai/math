import OAI.Computability.NearSquareRoot.PrecisionDiagonal
import Mathlib.Algebra.Order.Round

/-! # Fixed-point convolution and exact recovery

We use the Euclidean norm on an entire array, including its padded coordinates.
The scale `q` in the manuscript is `2^k`. The individual complex products and
the final rescaling may each introduce an error of up to `q ^ (-70 : ℤ)`
per coordinate. Both forward transforms and the adjoint are rounded as well.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

variable {ι : Type*} [Fintype ι]

/-- Coordinatewise complex multiplication of two padded transform arrays. -/
def pointwiseProduct (x y : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => x i * y i)

theorem norm_pointwiseProduct_le (x y : EuclideanSpace ℂ ι) :
    ‖pointwiseProduct x y‖ ≤ ‖x‖ * ‖y‖ := by
  apply euclidean_norm_le_mul_of_coordinates _ y (norm_nonneg x)
  intro i
  change ‖x i * y i‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x i) (norm_nonneg _)

theorem pointwiseProduct_error (x y x' y' : EuclideanSpace ℂ ι) :
    ‖pointwiseProduct x' y' - pointwiseProduct x y‖ ≤
      ‖x' - x‖ * ‖y'‖ + ‖x‖ * ‖y' - y‖ := by
  have eqn : pointwiseProduct x' y' - pointwiseProduct x y =
      pointwiseProduct (x' - x) y' + pointwiseProduct x (y' - y) := by
    ext i
    change x' i * y' i - x i * y i = (x' i - x i) * y' i + x i * (y' i - y i)
    ring
  rw [eqn]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_pointwiseProduct_le ..) (norm_pointwiseProduct_le ..))

private theorem addDyadic {q x y : ℝ} (hq : 2 ≤ q) {e : ℤ}
    (hx : x ≤ q ^ e) (hy : y ≤ q ^ e) : x + y ≤ q ^ (e + 1) := by
  have hq' : 0 < q := by linarith
  rw [zpow_add₀ hq'.ne', zpow_one]
  calc
    _ ≤ q ^ e + q ^ e := add_le_add hx hy
    _ = q ^ e * 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hq (zpow_nonneg hq'.le _)

private theorem mulDyadic {q x y : ℝ} (hq : 0 < q) {a b : ℤ} (hy : 0 ≤ y)
    (hx : x ≤ q ^ a) (hy' : y ≤ q ^ b) : x * y ≤ q ^ (a + b) := by
  rw [zpow_add₀ hq.ne']
  exact mul_le_mul hx hy' hy (zpow_nonneg hq.le _)

private theorem dyadicMono {q : ℝ} (hq : 2 ≤ q) {a b : ℤ} (h : a ≤ b) :
    q ^ a ≤ q ^ b := zpow_le_zpow_right₀ (by linarith) h

/-- Entrywise grid errors on all padded records, measured in the Euclidean norm. -/
private theorem arrayRoundoff {q : ℝ} (hq : 2 ≤ q) (hdim : (Fintype.card ι : ℝ) ≤ q)
    (x y : EuclideanSpace ℂ ι) (h : ∀ i, ‖x i - y i‖ ≤ q ^ (-70 : ℤ)) :
    ‖x - y‖ ≤ q ^ (-69 : ℤ) := by
  have hq' : 0 < q := by linarith
  have hs : Real.sqrt (Fintype.card ι) ≤ q := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hq'.le, hdim.trans (by nlinarith)⟩
  have he := euclidean_norm_le_of_coordinates (x - y) (zpow_nonneg hq'.le (-70)) h
  apply he.trans
  apply mulDyadic (a := 1) (b := -70) hq' (zpow_nonneg hq'.le _)
  · simpa using hs
  · rfl

/-- Bounds on the stored pointwise product, including rounding each complex
record after multiplication. The second bound admits this array as an input
to the rounded adjoint. -/
theorem roundedProductBounds {q : ℝ} (hq : 2 ≤ q) (hdim : (Fintype.card ι : ℝ) ≤ q)
    {x y x' y' p : EuclideanSpace ℂ ι}
    (hx : ‖x‖ ≤ q ^ (4 : ℤ)) (hy : ‖y‖ ≤ q ^ (4 : ℤ))
    (hex : ‖x' - x‖ ≤ q ^ (-40 : ℤ)) (hey : ‖y' - y‖ ≤ q ^ (-40 : ℤ))
    (hp : ∀ i, ‖p i - x' i * y' i‖ ≤ q ^ (-70 : ℤ)) :
    ‖p - pointwiseProduct x y‖ ≤ q ^ (-30 : ℤ) ∧ ‖p‖ ≤ q ^ (12 : ℤ) := by
  have hq' : 0 < q := by linarith
  have hy' : ‖y'‖ ≤ q ^ (5 : ℤ) := by
    calc
      ‖y'‖ ≤ ‖y' - y‖ + ‖y‖ := by simpa using norm_add_le (y' - y) y
      _ ≤ _ := addDyadic hq (hey.trans (dyadicMono hq (by decide : (-40 : ℤ) ≤ 4))) hy
  have hxy := mulDyadic hq' (norm_nonneg _) hex hy'
  have hyx := mulDyadic hq' (norm_nonneg _) hx hey
  have habs : ‖pointwiseProduct x' y' - pointwiseProduct x y‖ ≤ q ^ (-34 : ℤ) :=
    (pointwiseProduct_error ..).trans (addDyadic hq hxy
      (hyx.trans (dyadicMono hq (by decide : (4 : ℤ) + -40 ≤ -40 + 5))))
  have hr := arrayRoundoff hq hdim p (pointwiseProduct x' y') hp
  have herr : ‖p - pointwiseProduct x y‖ ≤ q ^ (-30 : ℤ) := by
    calc
      _ ≤ _ := norm_sub_le_norm_sub_add_norm_sub p (pointwiseProduct x' y') _
      _ ≤ q ^ (-33 : ℤ) := addDyadic hq (hr.trans (dyadicMono hq (by decide))) habs
      _ ≤ _ := dyadicMono hq (by decide)
  have hprod : ‖pointwiseProduct x y‖ ≤ q ^ (8 : ℤ) :=
    (norm_pointwiseProduct_le ..).trans (mulDyadic hq' (norm_nonneg _) hx hy)
  refine ⟨herr, ?_⟩
  calc
    _ ≤ ‖p - pointwiseProduct x y‖ + ‖pointwiseProduct x y‖ := by
      simpa using norm_add_le (p - pointwiseProduct x y) (pointwiseProduct x y)
    _ ≤ q ^ (9 : ℤ) := addDyadic hq (herr.trans (dyadicMono hq (by decide))) hprod
    _ ≤ _ := dyadicMono hq (by decide)

/-- With the manuscript's precision allowances, the rounded product, adjoint,
rescaling and output rounding recover every integral real component of the
ideal convolution. The adjoint implementation need only meet its accuracy
bound on inputs of norm at most `q ^ 12`. -/
theorem roundedConvolutionRecovers {q : ℝ} (hq : 2 ≤ q) (hdim : (Fintype.card ι : ℝ) ≤ q)
    (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    {a b x' y' p w out : EuclideanSpace ℂ ι} {s s' : ℝ}
    (hadjoint : ‖p‖ ≤ q ^ (12 : ℤ) → ‖w - U.symm p‖ ≤ q ^ (-40 : ℤ))
    (ha : ‖a‖ ≤ q ^ (4 : ℤ)) (hb : ‖b‖ ≤ q ^ (4 : ℤ))
    (hex : ‖x' - U a‖ ≤ q ^ (-40 : ℤ)) (hey : ‖y' - U b‖ ≤ q ^ (-40 : ℤ))
    (hp : ∀ i, ‖p i - x' i * y' i‖ ≤ q ^ (-70 : ℤ))
    (hs : |s| ≤ q) (hes : |s' - s| ≤ q ^ (-70 : ℤ))
    (hout : ∀ i, ‖out i - s' • w i‖ ≤ q ^ (-70 : ℤ)) :
    let exactOutput := s • U.symm (pointwiseProduct (U a) (U b))
    ‖out - exactOutput‖ ≤ 1 / 4 ∧
      ∀ (i : ι) (z : ℤ), (exactOutput i).re = z → round (out i).re = z := by
  let v := pointwiseProduct (U a) (U b)
  have hq' : 0 < q := by linarith
  obtain ⟨he, hpm⟩ := roundedProductBounds hq hdim (by simpa using ha)
    (by simpa using hb) hex hey hp
  have hw : ‖w - U.symm v‖ ≤ q ^ (-29 : ℤ) := by
    calc
      _ ≤ ‖w - U.symm p‖ + ‖U.symm p - U.symm v‖ := norm_sub_le_norm_sub_add_norm_sub ..
      _ = ‖w - U.symm p‖ + ‖p - v‖ := by rw [← map_sub, U.symm.norm_map]
      _ ≤ _ := addDyadic hq ((hadjoint hpm).trans (dyadicMono hq (by decide))) he
  have hm : ‖w‖ ≤ q ^ (13 : ℤ) := by
    calc
      _ ≤ ‖w - U.symm p‖ + ‖U.symm p‖ := by simpa using norm_add_le (w - U.symm p) (U.symm p)
      _ ≤ _ := addDyadic hq ((hadjoint hpm).trans (dyadicMono hq (by decide : (-40 : ℤ) ≤ 12))) (by simpa using hpm)
  have hscale : s' • w - s • U.symm v = (s' - s) • w + s • (w - U.symm v) := by
    rw [sub_smul, smul_sub]
    abel
  have hse : ‖s' • w - s • U.symm v‖ ≤ q ^ (-27 : ℤ) := by
    rw [hscale]
    apply (norm_add_le ..).trans
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have ha' := mulDyadic hq' (norm_nonneg _) hes hm
    have hb' := mulDyadic (a := 1) hq' (norm_nonneg _) (by simpa using hs) hw
    exact addDyadic hq (ha'.trans (dyadicMono hq (by decide))) hb'
  have hfinal : ‖out - s • U.symm v‖ ≤ 1 / 4 := by
    have hr := arrayRoundoff hq hdim out (s' • w) hout
    calc
      _ ≤ _ := norm_sub_le_norm_sub_add_norm_sub out (s' • w) _
      _ ≤ q ^ (-26 : ℤ) := addDyadic hq (hr.trans (dyadicMono hq (by decide))) hse
      _ ≤ q ^ (-2 : ℤ) := dyadicMono hq (by decide)
      _ ≤ 1 / 4 := by rw [zpow_neg, zpow_ofNat, inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
  refine ⟨hfinal, ?_⟩
  intro i z hz
  have h := (Complex.abs_re_le_norm ((out - s • U.symm v) i)).trans
    (PiLp.norm_apply_le (out - s • U.symm v) i)
  have h' : |(out i).re - (z : ℝ)| < 1 / 2 := by
    change ((s • U.symm v) i).re = (z : ℝ) at hz
    simpa only [PiLp.sub_apply, Complex.sub_re, hz] using h.trans_lt (hfinal.trans_lt (by norm_num : (1 : ℝ) / 4 < 1 / 2))
  rw [round_eq_iff]
  obtain ⟨h₁,h₂⟩ := abs_sub_lt_iff.mp h'
  exact ⟨by linarith, by linarith⟩

end NearSquareRoot
end Computability
end OAI
