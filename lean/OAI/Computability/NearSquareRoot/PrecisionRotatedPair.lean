import OAI.Computability.NearSquareRoot.PrecisionPhaseNormalization

/-! # Computing the Walsh-rotated dilation pair

For the chirp multiplier `z`, the top row of the product of the normalized
Walsh matrix and its two-coordinate dilation supplies the phases for all three
Walsh rounds. The following rational computation uses two integer square roots
and has absolute error at most four times the combined input and grid errors.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

/-- Rounded Walsh coefficient, obtained by halving the dyadic square root of two. -/
def walshRat (p : ℕ) : ℚ := sqrtRat p 2 / 2

/-- Rounded off-diagonal entry of the two-coordinate unitary dilation. -/
def dilationTailRat (p : ℕ) (q : ℚ × ℚ) : ℚ := sqrtRat p (1 - normSqRat q)

/-- Approximation to the first column entry of the rotated pair's top row. -/
def rotatedA (p : ℕ) (q : ℚ × ℚ) : ℚ × ℚ :=
  (walshRat p * (q.1 + dilationTailRat p q), walshRat p * q.2)

/-- Approximation to the second column entry of the rotated pair's top row. -/
def rotatedB (p : ℕ) (q : ℚ × ℚ) : ℚ × ℚ :=
  (walshRat p * (dilationTailRat p q - q.1), walshRat p * q.2)

private theorem cast_rotatedA (p : ℕ) (q : ℚ × ℚ) :
    toComplex (rotatedA p q) =
      (walshRat p : ℂ) * (toComplex q + (dilationTailRat p q : ℂ)) := by
  apply Complex.ext <;> simp [toComplex, rotatedA, Complex.mul_re, Complex.mul_im]

private theorem cast_rotatedB (p : ℕ) (q : ℚ × ℚ) :
    toComplex (rotatedB p q) =
      (walshRat p : ℂ) * ((dilationTailRat p q : ℂ) - star (toComplex q)) := by
  apply Complex.ext <;> simp [toComplex, rotatedB, Complex.mul_re, Complex.mul_im]

private theorem walshRat_error (p : ℕ) :
    0 ≤ (walshRat p : ℝ) ∧ (walshRat p : ℝ) ≤ 1 ∧
    |(walshRat p : ℝ) - (Real.sqrt 2)⁻¹| ≤ 1 / (2 : ℝ) ^ p := by
  obtain ⟨hl, hu⟩ := sqrtRat_interval p 2 (by norm_num)
  simp only [Rat.cast_ofNat] at hl hu
  have hs := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
  have hrewrite : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    field_simp
    nlinarith
  have hwr : (walshRat p : ℝ) = (sqrtRat p 2 : ℝ) / 2 := by simp [walshRat]
  rw [hwr, hrewrite]
  refine ⟨?_, ?_, ?_⟩
  · unfold sqrtRat
    positivity
  · nlinarith [Real.sqrt_nonneg 2]
  · rw [abs_le]
    constructor <;> linarith [show 0 < 1 / (2 : ℝ) ^ p by positivity]

private theorem rotationTail_lipschitz (x y : ℝ) (hx₀ : 0 ≤ x) (hy₀ : 0 ≤ y)
    (hx : x ≤ 3 / 4) (hy : y ≤ 3 / 4) :
    |Real.sqrt (1 - x ^ 2) - Real.sqrt (1 - y ^ 2)| ≤ 2 * |x - y| := by
  have lower (z : ℝ) (hz₀ : 0 ≤ z) (hz : z ≤ 3 / 4) :
      (1 / 2 : ℝ) ≤ Real.sqrt (1 - z ^ 2) ∧
        Real.sqrt (1 - z ^ 2) ^ 2 = 1 - z ^ 2 := by
    have hz₂ : z ^ 2 ≤ (3 / 4 : ℝ) ^ 2 := by gcongr
    have hs := Real.sq_sqrt (show 0 ≤ 1 - z ^ 2 by nlinarith)
    have hn := Real.sqrt_nonneg (1 - z ^ 2)
    exact ⟨by nlinarith, hs⟩
  obtain ⟨hlx, hsx⟩ := lower x hx₀ hx
  obtain ⟨hly, hsy⟩ := lower y hy₀ hy
  let a := Real.sqrt (1 - x ^ 2)
  let b := Real.sqrt (1 - y ^ 2)
  change 1 / 2 ≤ a at hlx
  change 1 / 2 ≤ b at hly
  change a ^ 2 = _ at hsx
  change b ^ 2 = _ at hsy
  calc |a - b| ≤ |a - b| * (a + b) :=
          le_mul_of_one_le_right (abs_nonneg _) (by linarith)
       _ = |(a - b) * (a + b)| := by
          rw [abs_mul, abs_of_nonneg (show 0 ≤ a + b by linarith)]
       _ = |(y - x) * (x + y)| := by congr 1; nlinarith
       _ = |x - y| * (x + y) := by
          rw [abs_mul, abs_sub_comm y x, abs_of_nonneg (add_nonneg hx₀ hy₀)]
       _ ≤ 2 * |x - y| := by
          rw [mul_comm (2 : ℝ)]
          exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)

theorem rotatedPair_error (p : ℕ) (q : ℚ × ℚ) (z : ℂ) (ε : ℝ)
    (hz : ‖z‖ ≤ 1 / 2) (hq : ‖toComplex q - z‖ ≤ ε) (hε : ε ≤ 1 / 4) :
    let t := Real.sqrt (1 - ‖z‖ ^ 2)
    let h := (Real.sqrt 2)⁻¹
    ‖toComplex (rotatedA p q) - (h : ℂ) * (z + t)‖ ≤ 4 * (ε + 1 / (2 : ℝ) ^ p) ∧
    ‖toComplex (rotatedB p q) - (h : ℂ) * ((t : ℂ) - star z)‖ ≤
      4 * (ε + 1 / (2 : ℝ) ^ p) := by
  let δ : ℝ := 1 / (2 : ℝ) ^ p
  let t := Real.sqrt (1 - ‖z‖ ^ 2)
  let h := (Real.sqrt 2)⁻¹
  let r : ℝ := dilationTailRat p q
  let g : ℝ := walshRat p
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hε₀ := (norm_nonneg _).trans hq
  have hdiff := (abs_norm_sub_norm_le (toComplex q) z).trans hq
  have hqmag : ‖toComplex q‖ ≤ 3 / 4 := by linarith [(abs_le.mp hdiff).2]
  have hqrad : 0 ≤ 1 - normSqRat q := by
    apply (Rat.cast_nonneg (K := ℝ)).mp
    rw [Rat.cast_sub, Rat.cast_one, normSqRat_cast]
    nlinarith [mul_self_le_mul_self (norm_nonneg _) hqmag]
  obtain ⟨hrlo, hrhi⟩ := sqrtRat_interval p (1 - normSqRat q) hqrad
  rw [Rat.cast_sub, Rat.cast_one, normSqRat_cast] at hrlo hrhi
  change r ≤ _ at hrlo
  change _ < r + δ at hrhi
  have hrad := rotationTail_lipschitz ‖toComplex q‖ ‖z‖ (norm_nonneg _) (norm_nonneg _) hqmag
    (by linarith)
  change |Real.sqrt (1 - ‖toComplex q‖ ^ 2) - t| ≤ _ at hrad
  have hrt : |r - t| ≤ 2 * ε + δ := by
    rw [abs_le] at hrad ⊢
    constructor <;> linarith [hrad.1, hrad.2]
  have hrtC : ‖(r : ℂ) - (t : ℂ)‖ ≤ 2 * ε + δ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hrt
  have ht₀ : 0 ≤ t := Real.sqrt_nonneg _
  have ht₁ : t ≤ 1 := by
    dsimp [t]
    rw [Real.sqrt_le_iff]
    exact ⟨zero_le_one, by nlinarith [sq_nonneg ‖z‖]⟩
  have htC : ‖(t : ℂ)‖ ≤ 1 := by rwa [Complex.norm_of_nonneg ht₀]
  obtain ⟨hg₀, hg₁, hgh⟩ := walshRat_error p
  change 0 ≤ g at hg₀
  change g ≤ 1 at hg₁
  change |g - h| ≤ δ at hgh
  have common (W V : ℂ) (hW : ‖W‖ ≤ 2) (he : ‖V - W‖ ≤ 3 * ε + δ) :
      ‖(g : ℂ) * V - (h : ℂ) * W‖ ≤ 4 * (ε + δ) := calc
    _ = ‖(g : ℂ) * (V - W) + ((g - h : ℝ) : ℂ) * W‖ := by
      congr 1; push_cast; ring
    _ ≤ ‖(g : ℂ) * (V - W)‖ + ‖((g - h : ℝ) : ℂ) * W‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul, norm_mul, Complex.norm_of_nonneg hg₀, Complex.norm_real, Real.norm_eq_abs]
      have hp := mul_le_mul hg₁ he (norm_nonneg _) zero_le_one
      have hs := mul_le_mul hgh hW (norm_nonneg _) hδ.le
      linarith
  simp only [cast_rotatedA, cast_rotatedB]
  change ‖(g : ℂ) * (toComplex q + r) - (h : ℂ) * (z + t)‖ ≤ 4 * (ε + δ) ∧
    ‖(g : ℂ) * ((r : ℂ) - star (toComplex q)) - (h : ℂ) * ((t : ℂ) - star z)‖ ≤
      4 * (ε + δ)
  constructor
  · apply common
    · linarith [norm_add_le z (t : ℂ)]
    · rw [show toComplex q + (r : ℂ) - (z + (t : ℂ)) =
          (toComplex q - z) + ((r : ℂ) - (t : ℂ)) by ring]
      linarith [norm_add_le (toComplex q - z) ((r : ℂ) - (t : ℂ))]
  · apply common
    · have hstar : ‖star z‖ = ‖z‖ := by simp
      linarith [norm_sub_le (t : ℂ) (star z)]
    · rw [show (r : ℂ) - star (toComplex q) - ((t : ℂ) - star z) =
          ((r : ℂ) - (t : ℂ)) - star (toComplex q - z) by rw [star_sub]; ring]
      have hs : ‖star (toComplex q - z)‖ = ‖toComplex q - z‖ := norm_star _
      linarith [norm_sub_le ((r : ℂ) - (t : ℂ)) (star (toComplex q - z))]

/-- Complex dyadic number with two signed numerators at common precision. -/
def dyadicPair (p : ℕ) (x y : ℤ) : ℚ × ℚ := (x / (2 : ℚ)^p, y / (2 : ℚ)^p)

/-- Exact relation between the two rational output entries and their signed
integer implementation. Common denominators are powers of two and the two
intermediate square roots are taken on unsigned integers. -/
theorem rotatedPair_dyadic (p : ℕ) (x y : ℤ) :
    let s : ℤ := 2 ^ p
    let t : ℤ := Nat.sqrt ((s * s - x * x - y * y).toNat)
    let w : ℤ := Nat.sqrt (2 * ((2 : ℕ) ^ p) ^ 2)
    rotatedA p (dyadicPair p x y) = dyadicPair (2*p+1) (w * (x+t)) (w * y) ∧
    rotatedB p (dyadicPair p x y) = dyadicPair (2*p+1) (w * (t-x)) (w * y) := by
  let s : ℤ := 2 ^ p
  let t : ℤ := Nat.sqrt ((s * s - x * x - y * y).toNat)
  let w : ℤ := Nat.sqrt (2 * ((2 : ℕ) ^ p) ^ 2)
  let q := dyadicPair p x y
  have hsq : (1 - normSqRat q) * ((2 : ℚ)^p)^2 = (↑(s*s-x*x-y*y) : ℚ) := by
    dsimp [q, normSqRat, dyadicPair, s]
    push_cast
    field_simp
    ring
  have ht : dilationTailRat p q = (t : ℚ) / 2^p := by
    rw [dilationTailRat, sqrtRat, hsq, ← Int.floor_toNat, Int.floor_intCast]
    simp [t]
  have hw : walshRat p = (w : ℚ) / (2^p * 2) := by
    unfold walshRat sqrtRat
    rw [show 2 * ((2 : ℚ)^p)^2 = ((2*((2 : ℕ)^p)^2 : ℕ) : ℚ) by push_cast; rfl,
      Nat.floor_natCast]
    simp [w, div_div]
  change rotatedA p q = _ ∧ rotatedB p q = _
  have hs : (2 : ℚ)^(2*p+1) = ((2 : ℚ)^p)^2 * 2 := by
    rw [pow_succ, Nat.mul_comm, pow_mul]
  simp only [rotatedA, rotatedB, ht, hw]
  change ((w : ℚ) / (2^p * 2) * (x / (2 : ℚ)^p + t / (2 : ℚ)^p),
      (w : ℚ) / (2^p * 2) * (y / (2 : ℚ)^p)) = dyadicPair (2*p+1) (w * (x+t)) (w*y) ∧
    ((w : ℚ) / (2^p * 2) * (t / (2 : ℚ)^p - x / (2 : ℚ)^p),
      (w : ℚ) / (2^p * 2) * (y / (2 : ℚ)^p)) = dyadicPair (2*p+1) (w * (t-x)) (w*y)
  simp only [dyadicPair, hs, Prod.mk.injEq, Int.cast_mul, Int.cast_add, Int.cast_sub]
  constructor <;> constructor <;> field_simp

/-- Magnitudes of the integer intermediate words used by the rotated pair. -/
theorem rotatedPair_numerator_bounds (p : ℕ) (x y : ℤ)
    (hx : |x| ≤ 2 ^ p) (hy : |y| ≤ 2 ^ p) :
    let s : ℤ := 2 ^ p
    let t : ℤ := Nat.sqrt ((s * s - x * x - y * y).toNat)
    let w : ℤ := Nat.sqrt (2 * (2 ^ p) ^ 2)
    t ≤ s ∧ w ≤ 2 * s ∧
      |w * (x + t)| ≤ 4 * s ^ 2 ∧ |w * y| ≤ 4 * s ^ 2 ∧
      |w * (t - x)| ≤ 4 * s ^ 2 ∧ 4 * s ^ 2 < 2 ^ (2 * p + 3) := by
  let s : ℤ := 2 ^ p
  let t : ℤ := Nat.sqrt ((s * s - x * x - y * y).toNat)
  let w : ℤ := Nat.sqrt (2 * (2 ^ p) ^ 2)
  change t ≤ s ∧ w ≤ 2 * s ∧ |w * (x + t)| ≤ 4 * s ^ 2 ∧ |w * y| ≤ 4 * s ^ 2 ∧
    |w * (t - x)| ≤ 4 * s ^ 2 ∧ 4 * s ^ 2 < 2 ^ (2 * p + 3)
  have hs : 0 < s := by dsimp [s]; positivity
  have ht₀ : 0 ≤ t := by dsimp [t]; positivity
  have hw₀ : 0 ≤ w := by dsimp [w]; positivity
  have hrad : s * s - x * x - y * y ≤ s * s := by
    nlinarith [sq_nonneg x, sq_nonneg y]
  have hradNat : (s * s - x * x - y * y).toNat ≤ 2^p * 2^p := by
    apply (Int.toNat_le_toNat hrad).trans_eq
    rw [show s * s = ((2 ^ p * 2 ^ p : ℕ) : ℤ) by push_cast; rfl, Int.toNat_natCast]
  have ht : t ≤ s := by
    change ((Nat.sqrt _) : ℤ) ≤ (2 : ℤ)^p
    exact_mod_cast (by simpa using Nat.sqrt_le_sqrt hradNat :
      Nat.sqrt (s * s - x * x - y * y).toNat ≤ 2^p)
  have hw : w ≤ 2 * s := by
    have h : 2 * (2 ^ p) ^ 2 ≤ (2 * 2 ^ p : ℕ) * (2 * 2 ^ p) := by nlinarith
    change ((Nat.sqrt _) : ℤ) ≤ 2 * (2 : ℤ)^p
    exact_mod_cast (by simpa using Nat.sqrt_le_sqrt h :
      Nat.sqrt (2 * (2 ^ p) ^ 2) ≤ 2 * 2^p)
  have bound (v : ℤ) (hv : |v| ≤ 2 * s) : |w * v| ≤ 4 * s ^ 2 := by
    rw [abs_mul, abs_of_nonneg hw₀]
    calc w * |v| ≤ (2 * s) * (2 * s) := mul_le_mul hw hv (abs_nonneg _) (by omega)
         _ = 4 * s ^ 2 := by ring
  have hx' : |x| ≤ s := hx
  have hy' : |y| ≤ s := hy
  refine ⟨ht, hw, bound _ ?_, bound _ (by omega), bound _ ?_, ?_⟩
  · exact (abs_add_le _ _).trans (by rw [abs_of_nonneg ht₀]; omega)
  · exact (abs_sub _ _).trans (by rw [abs_of_nonneg ht₀]; omega)
  · change 4 * ((2 : ℤ) ^ p) ^ 2 < 2 ^ (2 * p + 3)
    rw [mul_comm 2 p, pow_add, pow_mul]
    norm_num
    nlinarith [sq_pos_of_pos hs]

end PhaseTable

end NearSquareRoot
end Computability
end OAI
