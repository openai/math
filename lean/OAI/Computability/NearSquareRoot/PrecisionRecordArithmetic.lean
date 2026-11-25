import OAI.Computability.NearSquareRoot.Precision
import OAI.Computability.NearSquareRoot.PrecisionGrid

/-! # Recovering digit convolution in fixed-width records

The two coordinatewise multiplies below are P192's signed encoded complex
multiplication with its actual truncating shifts. The resulting norm bound supplies the quarter-unit margin used by the
add-half-then-shift routine in `PrecisionRecovery`.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication

variable {ι : Type*} [Fintype ι]

noncomputable def recordArray {k : ℕ} (r : ι → Record k) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => value k (r i))

/-- Complex records written by the pointwise product pass. -/
def productArray {k : ℕ} (x y : ι → Record k) : ι → Record k :=
  fun i => multiply k (x i) (y i)

private theorem subarray_bound {q : ℝ} (hq : 2 ≤ q) (x y : EuclideanSpace ℂ ι)
    {a b : ℤ} (h : a ≤ b) (herr : ‖x - y‖ ≤ q ^ a) (hn : ‖y‖ ≤ q ^ b) :
    ‖x‖ ≤ q ^ (b+1) := by
  have hq' : 0 < q := by linarith
  have h₂ := (zpow_le_zpow_right₀ (by linarith : 1 ≤ q) h)
  calc
    _ ≤ ‖x-y‖ + ‖y‖ := norm_le_norm_sub_add _ _
    _ ≤ q^b + q^b := add_le_add (herr.trans h₂) hn
    _ ≤ _ := by rw [zpow_add₀ hq'.ne', zpow_one]; nlinarith [zpow_pos hq' b]

private theorem powerScale (k t : ℕ) :
    ((2 : ℝ)^k) ^ (t : ℤ) = (2 : ℝ)^(t*k) := by rw [zpow_natCast, ← pow_mul, Nat.mul_comm]

private theorem inverseScale (k t : ℕ) :
    ((2 : ℝ)^k) ^ (-(t : ℤ)) = 1 / (2 : ℝ)^(t*k) := by
  rw [zpow_neg, powerScale, one_div]

/-- Simultaneous local rounding and headroom of the actual pointwise product. -/
private theorem productArray_estimates {k : ℕ} (hk : 1 ≤ k) (hcard : Fintype.card ι ≤ 2^k)
    (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (a b : EuclideanSpace ℂ ι) (x y : ι → Record k)
    (ha : ‖a‖ ≤ (2 : ℝ)^(4*k)) (hb : ‖b‖ ≤ (2 : ℝ)^(4*k))
    (hx : ‖recordArray x - U a‖ ≤ 1 / (2 : ℝ)^(40*k))
    (hy : ‖recordArray y - U b‖ ≤ 1 / (2 : ℝ)^(40*k)) :
    (∀ j, ‖recordArray (productArray x y) j - recordArray x j * recordArray y j‖ ≤ 1 / (2:ℝ)^(70*k)) ∧
      ‖recordArray (productArray x y)‖ ≤ (2:ℝ)^(12*k) := by
  let q := (2 : ℝ)^k
  let p := recordArray (productArray x y)
  have hq : 2 ≤ q := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
  have hm : (Fintype.card ι : ℝ) ≤ q := by
    dsimp [q]
    exact_mod_cast hcard
  have pos (t : ℕ) : q^(t : ℤ) = (2 : ℝ)^(t*k) := powerScale k t
  have neg (t : ℕ) : q^(-(t : ℤ)) = 1 / (2 : ℝ)^(t*k) := inverseScale k t
  have e4 : q^(4 : ℤ) = (2 : ℝ)^(4*k) := pos 4
  have e12 : q^(12 : ℤ) = (2 : ℝ)^(12*k) := pos 12
  have e13 : q^(13 : ℤ) = (2 : ℝ)^(13*k) := pos 13
  have e40 : q^(-40 : ℤ) = 1 / (2 : ℝ)^(40*k) := neg 40
  have e70 : q^(-70 : ℤ) = 1 / (2 : ℝ)^(70*k) := neg 70
  have input (u : EuclideanSpace ℂ ι) (v : ι → Record k)
      (hu : ‖u‖ ≤ q^(4 : ℤ)) (hv : ‖recordArray v - U u‖ ≤ q^(-40 : ℤ))
      (j : ι) : ‖value k (v j)‖ ≤ (2 : ℝ)^(13*k) := by
    rw [← e13]
    exact (PiLp.norm_apply_le (recordArray v) j).trans <|
      (subarray_bound hq _ _ (by decide) hv (by simpa using hu)).trans
        (zpow_le_zpow_right₀ (by linarith) (by decide : (4 : ℤ) + 1 ≤ 13))
  rw [← e4] at ha hb
  rw [← e40] at hx hy
  have hp (j : ι) : ‖p j - (recordArray x) j * (recordArray y) j‖ ≤ q^(-70 : ℤ) := by
    rw [e70]
    exact multiply_error _ _ (input a x ha hx j) (input b y hb hy j)
  exact ⟨fun j => (hp j).trans_eq e70, (roundedProductBounds hq hm (by simpa using ha)
    (by simpa using hb) hx hy hp).2.trans_eq e12⟩

/-- The physical inverse transform receives an array inside its certified input range. -/
theorem productArray_input_bound {k : ℕ} (hk : 1 ≤ k) (hcard : Fintype.card ι ≤ 2^k)
    (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (a b : EuclideanSpace ℂ ι) (x y : ι → Record k)
    (ha : ‖a‖ ≤ (2 : ℝ)^(4*k)) (hb : ‖b‖ ≤ (2 : ℝ)^(4*k))
    (hx : ‖recordArray x - U a‖ ≤ 1 / (2 : ℝ)^(40*k))
    (hy : ‖recordArray y - U b‖ ≤ 1 / (2 : ℝ)^(40*k)) :
    ‖recordArray (productArray x y)‖ ≤ (2:ℝ)^(12*k) :=
  (productArray_estimates hk hcard U a b x y ha hb hx hy).2

/-- Error accounting through both rounded transforms, encoded pointwise
products, a rounded adjoint, and encoded rescaling. -/
theorem recordConvolution_error {k : ℕ} (hk : 1 ≤ k) (hcard : Fintype.card ι ≤ 2^k)
    (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (a b : EuclideanSpace ℂ ι) (x y w : ι → Record k) (scale : Record k)
    (s s' : ℝ) (hscale : value k scale = (s' : ℂ)) (hs : |s| ≤ (2 : ℝ)^k)
    (heScale : |s' - s| ≤ 1 / (2 : ℝ)^(70*k))
    (ha : ‖a‖ ≤ (2 : ℝ)^(4*k)) (hb : ‖b‖ ≤ (2 : ℝ)^(4*k))
    (hx : ‖recordArray x - U a‖ ≤ 1 / (2 : ℝ)^(40*k))
    (hy : ‖recordArray y - U b‖ ≤ 1 / (2 : ℝ)^(40*k))
    (hAdj : let p := recordArray (productArray x y)
            ‖p‖ ≤ (2 : ℝ)^(12*k) → ‖recordArray w - U.symm p‖ ≤ 1 / (2 : ℝ)^(40*k))
    : ‖recordArray (fun i => multiply k scale (w i)) -
        s • U.symm (pointwiseProduct (U a) (U b))‖ ≤ 1 / 4 := by
  let q := (2 : ℝ)^k
  let p := recordArray (productArray x y)
  let out := recordArray (fun j => multiply k scale (w j))
  have hq : 2 ≤ q := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
  have hm : (Fintype.card ι : ℝ) ≤ q := by
    dsimp [q]
    exact_mod_cast hcard
  have pos (t : ℕ) : q^(t : ℤ) = (2 : ℝ)^(t*k) := powerScale k t
  have neg (t : ℕ) : q^(-(t : ℤ)) = 1 / (2 : ℝ)^(t*k) := inverseScale k t
  have e4 : q^(4 : ℤ) = (2 : ℝ)^(4*k) := pos 4
  have e12 : q^(12 : ℤ) = (2 : ℝ)^(12*k) := pos 12
  have e13 : q^(13 : ℤ) = (2 : ℝ)^(13*k) := pos 13
  have e40 : q^(-40 : ℤ) = 1 / (2 : ℝ)^(40*k) := neg 40
  have e70 : q^(-70 : ℤ) = 1 / (2 : ℝ)^(70*k) := neg 70
  have est := productArray_estimates hk hcard U a b x y ha hb hx hy
  have hp (j : ι) : ‖p j - (recordArray x) j * (recordArray y) j‖ ≤ q^(-70 : ℤ) := (est.1 j).trans_eq e70.symm
  have hpm : ‖p‖ ≤ q^(12 : ℤ) := est.2.trans_eq e12.symm
  rw [← e4] at ha hb
  rw [← e40] at hx hy
  have hj : ‖p‖ ≤ q^(12 : ℤ) → ‖recordArray w - U.symm p‖ ≤ q^(-40 : ℤ) := by
    rw [e12, e40]
    exact hAdj
  have hw : ‖recordArray w‖ ≤ (2 : ℝ)^(13*k) := by
    rw [← e13]
    exact subarray_bound hq _ _ (by decide : (-40 : ℤ) ≤ 12) (hj hpm) (by simpa using hpm)
  have hsc : ‖value k scale‖ ≤ (2 : ℝ)^(13*k) := by
    rw [hscale, Complex.norm_real, Real.norm_eq_abs, ← e13]
    calc
      |s'| ≤ |s'-s|+|s| := by simpa using abs_add_le (s'-s) s
      _ ≤ q+q := by
        apply add_le_add _ hs
        rw [← e70] at heScale
        exact heScale.trans (by
          simpa using zpow_le_zpow_right₀ (by linarith : 1 ≤ q) (by decide : (-70 : ℤ) ≤ 1))
      _ ≤ q^(2 : ℤ) := by rw [zpow_ofNat]; nlinarith
      _ ≤ _ := zpow_le_zpow_right₀ (by linarith) (by decide)
  have ho (j : ι) : ‖out j - s' • (recordArray w) j‖ ≤ q^(-70 : ℤ) := by
    rw [e70]
    have he := multiply_error scale (w j) hsc ((PiLp.norm_apply_le (recordArray w) j).trans hw)
    rwa [hscale, ← Complex.real_smul] at he
  rw [← e70] at heScale
  exact (roundedConvolutionRecovers hq hm U hj ha hb hx hy hp hs heScale ho).1

end FixedPoint

end NearSquareRoot
end Computability
end OAI
