import OAI.Computability.IntegerMultiplication.Grid.Faith

/-!
# Width and accuracy of complex record multiplication

A complex record uses P192's signed pair of fixed-width words. Its multiplication
forms four full signed integer products, adds and subtracts them in pairs,
shifts both components towards zero, and re-encodes at the original width.
The integer headroom below covers products of two represented operands of norm
up to `2^(13k)`, including before the fractional bits are discarded.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication

/-- Fractional precision used for the full-array arithmetic. -/
def fractionBits (k : ℕ) := 70 * k + 1

/-- Width parameter of the balanced integer representation in a complex record. -/
def componentBits (k : ℕ) := 96 * k + 4

abbrev Record (k : ℕ) := Dusk.Grain (componentBits k)

noncomputable abbrev value (k : ℕ) (x : Record k) :=
  Grid.meaning (fractionBits k) (componentBits k) x

/-- Actual unsigned-word/sign operations executed by the encoded record product. -/
def multiply (k : ℕ) (x y : Record k) : Record k :=
  Grid.launch (x, Code.tally (fractionBits k), Dusk.mark y)

theorem multiply_encoding (k : ℕ) (x y : Record k) :
    Grid.adjust (Dusk.mark x, Code.tally (fractionBits k), Dusk.mark y) =
      Dusk.mark (multiply k x y) :=
  Grid.inject _ _

/-- Number of tape symbols in the encoded input or output record. -/
theorem record_size (k : ℕ) (x : Record k) :
    Code.size (Dusk.mark x) = 384 * k + 23 := by
  rw [Dusk.volume, componentBits]
  omega

private theorem product_norm_le {x y : ℂ} {k : ℕ}
    (hx : ‖x‖ ≤ (2 : ℝ) ^ (13 * k)) (hy : ‖y‖ ≤ (2 : ℝ) ^ (13 * k)) :
    ‖x * y‖ ≤ (2 : ℝ) ^ (26 * k) := by
  rw [norm_mul, show 26 * k = 13 * k + 13 * k by omega, pow_add]
  exact mul_le_mul hx hy (norm_nonneg _) (by positivity)

/-- Linear width suffices before returning the product to the stored grid. -/
theorem product_fits {x y : ℂ} {k : ℕ}
    (hx : ‖x‖ ≤ (2 : ℝ) ^ (13 * k)) (hy : ‖y‖ ≤ (2 : ℝ) ^ (13 * k)) :
    ‖x * y‖ * (2 : ℝ) ^ fractionBits k + 2 < (2 : ℝ) ^ componentBits k := by
  calc
    _ ≤ (2 : ℝ) ^ (26 * k) * 2 ^ fractionBits k + 2 := by
      gcongr; exact product_norm_le hx hy
    _ = (2 : ℝ) ^ (96 * k) * 2 + 2 := by
      rw [← pow_add, show 26 * k + fractionBits k = 96 * k + 1 by
        unfold fractionBits; omega, pow_succ]
    _ < (2 : ℝ) ^ componentBits k := by
      rw [componentBits, pow_add]
      norm_num
      linarith [show 1 ≤ (2 : ℝ) ^ (96 * k) from one_le_pow₀ (by norm_num)]

/-- Includes truncation of both signed components. -/
theorem multiply_error {k : ℕ} (x y : Record k)
    (hx : ‖value k x‖ ≤ (2 : ℝ) ^ (13 * k))
    (hy : ‖value k y‖ ≤ (2 : ℝ) ^ (13 * k)) :
    ‖value k (multiply k x y) - value k x * value k y‖ ≤ 1 / (2 : ℝ) ^ (70 * k) := by
  refine (Grid.confident (fractionBits k) x y (product_fits hx hy)).trans ?_
  rw [fractionBits, pow_succ]
  exact le_of_eq (by field_simp)

/-- Integer range of each of the four exact signed products feeding
the two accumulators in `Grid.timesG`, for all stored bit patterns. -/
theorem component_product_fits {k : ℕ} (x y : Record k) (u v : ℤ)
    (hu : u = (Grid.aspect x).re ∨ u = (Grid.aspect x).im)
    (hv : v = (Grid.aspect y).re ∨ v = (Grid.aspect y).im) :
    |u * v| < (2 : ℤ) ^ (2 * componentBits k) := by
  have coord (a : Record k) (t : ℤ)
      (h : t = (Grid.aspect a).re ∨ t = (Grid.aspect a).im) :
      |t| < (2 : ℤ) ^ componentBits k := by
    rcases h with rfl | rfl
    · exact (Grid.aspect_f a).1
    · exact (Grid.aspect_f a).2
  rw [abs_mul, two_mul, pow_add]
  exact (mul_le_mul_of_nonneg_right (coord x u hu).le (abs_nonneg v)).trans_lt
    (mul_lt_mul_of_pos_left (coord y v hv) (by positivity))

/-- Both components of the *unshifted* exact signed product fit in this many
magnitude bits. This is the intermediate held by `Grid.timesG`. -/
theorem unshifted_product_fits {k : ℕ} (x y : Record k)
    (hx : ‖value k x‖ ≤ (2 : ℝ) ^ (13 * k))
    (hy : ‖value k y‖ ≤ (2 : ℝ) ^ (13 * k)) :
    Grid.focus (166 * k + 3)
      (Grid.content (Grid.timesG (Grid.disp (Dusk.mark x), Grid.disp (Dusk.mark y)))) := by
  rw [Grid.key_M, Grid.pullG, Grid.pullG]
  apply Grid.short _ (Grid.into _)
  rw [map_mul, norm_mul]
  have component (a : Record k) (h : ‖value k a‖ ≤ (2 : ℝ) ^ (13 * k)) :
      ‖Grid.toC (Grid.aspect a)‖ ≤ (2 : ℝ) ^ (83 * k + 1) := by
    change ‖Grid.toC (Grid.aspect a) / (2 : ℂ) ^ fractionBits k‖ ≤ _ at h
    rw [norm_div, norm_pow, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num,
        div_le_iff₀ (by positivity), ← pow_add] at h
    simpa only [show 13 * k + fractionBits k = 83 * k + 1 by unfold fractionBits; omega] using h
  calc
    _ ≤ (2 : ℝ) ^ (83 * k + 1) * 2 ^ (83 * k + 1) :=
      mul_le_mul (component x hx) (component y hy) (norm_nonneg _) (by positivity)
    _ < (2 : ℝ) ^ (166 * k + 3) := by
      rw [← pow_add]
      exact pow_lt_pow_right₀ (by norm_num) (by omega)

end FixedPoint

end NearSquareRoot
end Computability
end OAI
