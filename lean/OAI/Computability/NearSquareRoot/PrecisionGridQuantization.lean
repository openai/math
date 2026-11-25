import OAI.Computability.IntegerMultiplication.Grid.Value
import OAI.Computability.IntegerMultiplication.Carry.Figure
import OAI.Computability.IntegerMultiplication.Code.Padding
import Mathlib.Algebra.Order.Round

/-! # Quantizing rational complex coefficients for the signed P192 record format

The source of a table entry is a pair of rationals, so component quantization is
executable even for a table prepared by a sequence approximation to a root of unity.
The separate comparison with the target coefficient accounts for that approximation.
For the final convolution scale, an encoded integer square-root program constructs
the signed record directly and incurs polynomial setup cost.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication

/-- The exact complex value of a rational real/imaginary pair. -/
def complexRat (a b : ℚ) : ℂ := ⟨a, b⟩

/-- Scale by a binary power and round both rational coordinates to integers. -/
def quantizedCell (p : ℕ) (a b : ℚ) : Grid.Cell :=
  ⟨round (a * (2 : ℚ) ^ p), round (b * (2 : ℚ) ^ p)⟩

/-- Store the signed rounded integer coordinates in a finite P192 record. -/
def quantize (p w : ℕ) (a b : ℚ) : Dusk.Grain w :=
  Grid.wrapMap w (quantizedCell p a b)

private theorem scaled_round_error (q : ℚ) (p : ℕ) :
    |(round (q * (2 : ℚ) ^ p) : ℝ) - (q : ℝ) * 2 ^ p| ≤ 1 / 2 := by
  have h := abs_sub_round (q * (2 : ℚ) ^ p)
  rw [abs_sub_comm] at h
  have hc := (Rat.cast_le (K := ℝ)).2 h
  push_cast at hc
  exact hc

private theorem scaled_round_abs (q : ℚ) (p : ℕ) :
    |(round (q * (2 : ℚ) ^ p) : ℝ)| ≤ |(q : ℝ)| * 2 ^ p + 1 / 2 := by
  let x : ℝ := round (q * (2 : ℚ) ^ p)
  let y : ℝ := (q : ℝ) * 2 ^ p
  calc |x| = |(x - y) + y| := by rw [sub_add_cancel]
       _ ≤ |x - y| + |y| := abs_add_le ..
       _ ≤ 1 / 2 + |y| := by gcongr; exact scaled_round_error q p
       _ = _ := by simp [y, abs_mul, add_comm]

/-- Sufficient headroom in either signed component, including rounding. -/
theorem quantizedCell_fits {p w : ℕ} {a b : ℚ}
    (h : ‖complexRat a b‖ * (2 : ℝ) ^ p + 1 / 2 < 2 ^ w) :
    Grid.focus w (quantizedCell p a b) := by
  apply Grid.short _ _ h
  constructor
  · exact (scaled_round_abs a p).trans (by gcongr; exact Complex.abs_re_le_norm (complexRat a b))
  · exact (scaled_round_abs b p).trans (by gcongr; exact Complex.abs_im_le_norm (complexRat a b))

/-- Complex Euclidean error in a single record, including its signed finite representation. -/
theorem quantize_error {p w : ℕ} {a b : ℚ}
    (h : ‖complexRat a b‖ * (2 : ℝ) ^ p + 1 / 2 < 2 ^ w) :
    ‖Grid.meaning p w (quantize p w a b) - complexRat a b‖ ≤ 1 / (2 : ℝ) ^ p := by
  rw [Grid.meaning, quantize, Grid.recovers _ (quantizedCell_fits h)]
  have hs : (2 : ℂ) ^ p ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [show (Grid.toC (quantizedCell p a b) / (2 : ℂ) ^ p - complexRat a b) =
      (Grid.toC (quantizedCell p a b) - complexRat a b * (2 : ℂ) ^ p) / (2 : ℂ) ^ p by
    field_simp]
  rw [norm_div, norm_pow, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  have hpow : (2 : ℂ) ^ p = ((2 : ℝ) ^ p : ℝ) := by push_cast; rfl
  simp [Grid.toC, quantizedCell, complexRat]
  rw [hpow]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_add]
  linarith [scaled_round_error a p, scaled_round_error b p]

/-- Error in the stored coefficient relative to the target from which the rational
table entry was computed. -/
theorem quantize_error_to_target {p w : ℕ} {a b : ℚ} {z : ℂ} {δ : ℝ}
    (h : ‖complexRat a b‖ * (2 : ℝ) ^ p + 1 / 2 < 2 ^ w)
    (hz : ‖complexRat a b - z‖ ≤ δ) :
    ‖Grid.meaning p w (quantize p w a b) - z‖ ≤ 1 / (2 : ℝ) ^ p + δ :=
  (norm_sub_le_norm_sub_add_norm_sub _ (complexRat a b) _).trans
    (add_le_add (quantize_error h) hz)

/-- Integer numerator of the downward-rounded square root on the grid of mesh `2⁻ᵖ`. -/
def sqrtNumerator (S p : ℕ) : ℕ :=
  Nat.sqrt (S * (2 ^ p) ^ 2)

theorem sqrtNumerator_interval (S p : ℕ) :
    (sqrtNumerator S p : ℝ) ≤ Real.sqrt S * (2 : ℝ) ^ p ∧
    Real.sqrt S * (2 : ℝ) ^ p < (sqrtNumerator S p : ℝ) + 1 := by
  have h : Real.sqrt ((S * (2 ^ p) ^ 2 : ℕ) : ℝ) = Real.sqrt S * (2 : ℝ) ^ p := by
    push_cast
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]
  rw [← h]
  exact ⟨Real.nat_sqrt_le_real_sqrt, Real.real_sqrt_lt_nat_sqrt_succ⟩

/-- Dividing the square root of the scaled natural input by the scale recovers
the target to within one unit in the last place, also on perfect squares. -/
theorem sqrtNumerator_error (S p : ℕ) :
    |(sqrtNumerator S p : ℝ) / 2 ^ p - Real.sqrt S| < 1 / (2 : ℝ) ^ p := by
  have hpos : 0 < (2 : ℝ) ^ p := by positivity
  obtain ⟨hl, hu⟩ := sqrtNumerator_interval S p
  have hv := (div_le_iff₀ hpos).mpr hl
  rw [abs_of_nonpos (sub_nonpos.mpr hv), neg_sub, sub_lt_iff_lt_add, ← add_div]
  exact (lt_div_iff₀ hpos).mpr (by linarith)

/-- For a box with `S ≤ 2^k` occupied cells, the stored numerator uses at most
`p + k + 1` binary digits. -/
theorem sqrtNumerator_lt_pow {S k : ℕ} (p : ℕ) (hS : S ≤ 2 ^ k) :
    sqrtNumerator S p < 2 ^ (p + k + 1) := by
  have h1 : 1 ≤ (2 : ℕ) ^ k := Nat.one_le_pow _ _ (by decide)
  have h2 : S ≤ (2 ^ k) ^ 2 := hS.trans (by nlinarith)
  have h3 : sqrtNumerator S p ≤ 2 ^ (p + k) := by
    unfold sqrtNumerator
    have h := Nat.sqrt_le_sqrt (Nat.mul_le_mul_right ((2 ^ p) ^ 2) h2)
    have he : (2 ^ k) ^ 2 * (2 ^ p) ^ 2 = (2 ^ (p + k) : ℕ) ^ 2 := by rw [pow_add]; ring
    rwa [he, Nat.sqrt_eq'] at h
  exact h3.trans_lt (by rw [pow_succ]; have := Nat.two_pow_pos (p+k); omega)

/-- Encode a nonnegative dyadic value by its integer numerator, without another rounding. -/
def encodeNumerator (w a : ℕ) : Dusk.Grain w :=
  Grid.wrapMap w (⟨a, 0⟩ : Grid.Cell)

theorem meaning_encodeNumerator {w a : ℕ} (p : ℕ) (ha : a < 2 ^ w) :
    Grid.meaning p w (encodeNumerator w a) = (a : ℂ) / 2 ^ p := by
  have hf : Grid.focus w (⟨a, 0⟩ : Grid.Cell) := by
    constructor
    · change |(a : ℤ)| < (2 : ℤ) ^ w
      rw [abs_of_nonneg (Int.natCast_nonneg _)]
      exact_mod_cast ha
    · change |(0 : ℤ)| < (2 : ℤ) ^ w
      rw [abs_zero]
      positivity
  rw [Grid.meaning, encodeNumerator, Grid.recovers _ hf]
  simp [Grid.toC]


/-- The finite P192 record used for the final real scale factor. -/
def sqrtRecord (p w S : ℕ) : Dusk.Grain w := encodeNumerator w (sqrtNumerator S p)

/-- The scale record is exactly real. -/
theorem sqrtRecord_value {S k w : ℕ} (p : ℕ) (hS : S ≤ 2 ^ k) (hw : p + k + 1 ≤ w) :
    Grid.meaning p w (sqrtRecord p w S) = (((sqrtNumerator S p : ℝ) / 2 ^ p : ℝ) : ℂ) := by
  have fit : sqrtNumerator S p < 2 ^ w :=
    (sqrtNumerator_lt_pow p hS).trans_le (Nat.pow_le_pow_right (by decide) hw)
  rw [sqrtRecord, meaning_encodeNumerator p fit]
  push_cast
  rfl

/-- Error in the actual decoded scale record; the headroom check uses only the padded box size. -/
theorem sqrtRecord_error {S k w : ℕ} (p : ℕ) (hS : S ≤ 2 ^ k) (hw : p + k + 1 ≤ w) :
    ‖Grid.meaning p w (sqrtRecord p w S) - (Real.sqrt S : ℂ)‖ < 1 / (2 : ℝ) ^ p := by
  rw [sqrtRecord_value p hS hw, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact sqrtNumerator_error S p

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits

/-- The scaled square-root numerator as a polynomial-time setup program on encoded
little-endian bit words. Its input is the unary fractional precision and the
binary box size; its output has exactly their combined length plus one. -/
def sqrtNumeratorWord (x : Tally × Word) : Word :=
  resize (() :: (x.1 ++ ruler x.2), Carry.rescue (shift (x.1, shift x)))

theorem sqrtNumeratorWord_poly : Poly sqrtNumeratorWord := by
  have hshift : Easy (fun x : Tally × Word => shift (x.1, shift x)) := by fun_prop
  have hwidth : Easy (fun x : Tally × Word => () :: (x.1 ++ ruler x.2)) := by fun_prop
  exact (hwidth.poly.pair (hshift.poly.compose Carry.rescuePoly)).compose
    ((easy_resize Easy.identity).poly)

theorem sqrtNumeratorWord_spec (t : Tally) (s : Word) :
    (sqrtNumeratorWord (t, s)).length = t.length + s.length + 1 ∧
    value (sqrtNumeratorWord (t, s)) = sqrtNumerator (value s) t.length := by
  let width := t.length + s.length + 1
  have hw : tally width = () :: (t ++ ruler s) := by
    convert recover_tally (() :: (t ++ ruler s)) using 1
    simp [width]
  change (resize (() :: (t ++ ruler s), _)).length = width ∧
    value (resize (() :: (t ++ ruler s), _)) = _
  rw [← hw]
  change (sized width _).length = _ ∧ value (sized width _) = _
  refine ⟨sized_length .., ?_⟩
  rw [sized_low, Carry.rescued, shift_value, shift_value]
  have h : 2 ^ t.length * (2 ^ t.length * value s) =
      value s * (2 ^ t.length) ^ 2 := by ring
  rw [h]
  exact Nat.mod_eq_of_lt (sqrtNumerator_lt_pow _ (value_lt s).le)

/-- Encode a nonnegative binary word as a fixed-width complex register with zero
imaginary part. The first argument is the unary component-width parameter. -/
def encodeNumeratorWord (x : Tally × Word) : Dusk.Pair :=
  (Dusk.plan (() :: x.1, x.2), Dusk.plan (() :: x.1, []))

theorem encodeNumeratorWord_easy : Easy encodeNumeratorWord := by
  have width : Easy (fun x : Tally × Word => () :: x.1) := by fun_prop
  exact ((width.pair Easy.snd).compose Dusk.planned).pair
    ((width.pair (Easy.const ([] : Word))).compose Dusk.planned)

theorem encodeNumeratorWord_spec (t : Tally) (s : Word) (h : value s < 2 ^ t.length) :
    encodeNumeratorWord (t,s) =
      Dusk.mark (⟨(value s : Dusk.day t.length), 0⟩ : Dusk.Grain t.length) := by
  have width : (() :: t).length = t.length + 1 := rfl
  have hperiod : value s < 2 * Dusk.period t.length := by
    have h1 := Dusk.period_s t.length
    rw [pow_succ] at h1
    omega
  have zero : value [] < 2 * Dusk.period t.length := by
    have := Dusk.certain t.length
    simp only [value_nil]
    omega
  simp [encodeNumeratorWord, Dusk.mark, Dusk.plan_lt width s hperiod, Dusk.plan_lt width [] zero]

/-- P192 setup procedure on unary precisions `(p,w)` and the binary box size. -/
def sqrtRecordWord (x : Tally × Tally × Word) : Dusk.Pair :=
  encodeNumeratorWord (x.2.1, sqrtNumeratorWord (x.1, x.2.2))

theorem sqrtRecordWord_poly : Poly sqrtRecordWord := by
  exact ((show Poly (fun x : Tally × Tally × Word => x.2.1) from by fun_prop).pair
    ((show Poly (fun x : Tally × Tally × Word => (x.1,x.2.2)) from by fun_prop).compose
      sqrtNumeratorWord_poly)).compose encodeNumeratorWord_easy.poly

theorem sqrtRecordWord_spec {k : ℕ} (p w : Tally) (s : Word)
    (hs : value s ≤ 2 ^ k) (hw : p.length + k + 1 ≤ w.length) :
    sqrtRecordWord (p, w, s) = Dusk.mark (sqrtRecord p.length w.length (value s)) := by
  have fit : value (sqrtNumeratorWord (p, s)) < 2 ^ w.length := by
    rw [(sqrtNumeratorWord_spec p s).2]
    exact (sqrtNumerator_lt_pow _ hs).trans_le (Nat.pow_le_pow_right (by decide) hw)
  rw [sqrtRecordWord, encodeNumeratorWord_spec _ _ fit, (sqrtNumeratorWord_spec p s).2]
  simp [sqrtRecord, encodeNumerator, Grid.wrapMap]

/-- The descriptor that supplies the two widths and the binary box size can prepare
the exact encoded scale record with polynomial setup cost. -/
theorem sqrtRecord_has {I : Type} {r : Strip.Regime I} {p w S k : I → ℕ}
    (hp : Staff.Realizes r p) (hw : Staff.Realizes r w) (hS : Carry.Figure r S)
    (hs : ∀ i, S i ≤ 2 ^ k i) (hwidth : ∀ i, p i + k i + 1 ≤ w i) :
    r.Has (fun i => Dusk.mark (sqrtRecord (p i) (w i) (S i))) := by
  obtain ⟨s, hsword, hval⟩ := hS
  have pword : r.Has (fun i => tally (p i)) := hp
  have wword : r.Has (fun i => tally (w i)) := hw
  have got := (pword.pair (wword.pair hsword)).thenDo sqrtRecordWord_poly
  have spec i := sqrtRecordWord_spec (k := k i) (tally (p i)) (tally (w i)) (s i)
    ((hval i).trans_le (hs i)) (by simpa only [tally_length] using hwidth i)
  have align i : sqrtRecordWord (tally (p i), tally (w i), s i) =
      Dusk.mark (sqrtRecord (p i) (w i) (S i)) := by
    rw [spec i, tally_length, tally_length, hval]
  simpa only [align] using got

end FixedPoint

end NearSquareRoot
end Computability
end OAI
