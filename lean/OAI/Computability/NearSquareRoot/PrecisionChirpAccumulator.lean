import OAI.Computability.IntegerMultiplication.Brief.Mantissa
import OAI.Computability.IntegerMultiplication.Grid.Faith
import OAI.Computability.NearSquareRoot.ShortWordCall

/-! # Computing scaled sums of quantized roots

The chirp table setup uses one common dyadic denominator for the root records.
The numerator of their sum is formed exactly on signed binary words. Multiplying
both components by the integer numerator of the reciprocal square root leaves
all rounding until the output.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits

/-- Sum the marked real and imaginary components separately, then scale each by
the same nonnegative binary integer. The output components have unrestricted width. -/
def scaledRootWords (x : Word × List Dusk.Pair) : Grid.Coef :=
  let rs := x.2.map Grid.disp
  let c := Brief.register x.1
  (Brief.times (c, Brief.wave (rs.map Prod.fst)),
   Brief.times (c, Brief.wave (rs.map Prod.snd)))

/-- A polynomial-time stack program for the encoded sum and subsequent scale. -/
theorem scaledRootWords_poly : Poly scaledRootWords := by
  have decode := Grid.disp_easy.poly
  have hf : Poly (Prod.fst : Grid.Coef → Grid.S) := Easy.fst.poly
  have hs : Poly (Prod.snd : Grid.Coef → Grid.S) := Easy.snd.poly
  unfold scaledRootWords
  fun_prop

private theorem sum_of_decoded (xs : List Grid.Coef) :
    ((xs.map Grid.content).sum).re = ((xs.map Prod.fst).map Grid.whole).sum ∧
    ((xs.map Grid.content).sum).im = ((xs.map Prod.snd).map Grid.whole).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [Grid.content, ih] at *

/-- Exact Gaussian integer numerator of the scaled row, for any list of marked
input grains, including the empty list. -/
theorem scaledRootWords_content {w : ℕ} (s : Word) (rows : List (Dusk.Grain w)) :
    Grid.content (scaledRootWords (s, rows.map Dusk.mark)) =
      (value s : Grid.Cell) * (rows.map Grid.aspect).sum := by
  let xs := (rows.map Dusk.mark).map Grid.disp
  have h : xs.map Grid.content = rows.map Grid.aspect := by
    simp [xs, List.map_map, Function.comp_def, Grid.pullG]
  obtain ⟨hr, hi⟩ := sum_of_decoded xs
  rw [h] at hr hi
  apply QuadraticAlgebra.ext
  · change Grid.whole (Brief.times (Brief.register s, Brief.wave (xs.map Prod.fst))) = _
    simp [Brief.regV, Brief.waveV, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast, hr]
  · change Grid.whole (Brief.times (Brief.register s, Brief.wave (xs.map Prod.snd))) = _
    simp [Brief.regV, Brief.waveV, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast, hi]

/-- After interpreting the root records with `p` fractional bits and the
scalar with `q` fractional bits, the encoded numerator needs `p + q`
fractional bits and represents the exact scaled complex sum. -/
theorem scaledRootWords_meaning {w : ℕ} (p q : ℕ) (s : Word) (rows : List (Dusk.Grain w)) :
    Grid.toC (Grid.content (scaledRootWords (s, rows.map Dusk.mark))) / (2 : ℂ)^(p+q) =
      ((value s : ℂ) / 2^q) * (rows.map (Grid.meaning p w)).sum := by
  rw [scaledRootWords_content, map_mul, map_natCast, map_list_sum]
  have hs : (rows.map (Grid.meaning p w)).sum = (List.map (fun x => Grid.toC (Grid.aspect x)) rows).sum / 2^p := by
    induction rows with
    | nil => simp
    | cons a l ih => simp [ih, Grid.meaning, add_div]
  rw [hs, List.map_map, pow_add]
  simp only [Function.comp_def]
  ring

/-- Truncate both signed components after the entire exact accumulation. -/
def shiftedRootWords (x : Tally × Word × List Dusk.Pair) : Grid.Coef :=
  Grid.rest (x.1, scaledRootWords x.2)

theorem shiftedRootWords_poly : Poly shiftedRootWords :=
  (Easy.fst.poly.pair (Easy.snd.poly.compose scaledRootWords_poly)).compose Grid.rest_easy.poly

/-- Exact query size for the physical setup bound. Since each table row has bounded
length and record width, a polynomial in this size is a polynomial setup cost. -/
theorem shiftedRootWords_input_size {w : ℕ} (q : ℕ) (s : Word) (rows : List (Dusk.Grain w)) :
    size (tally q, s, rows.map Dusk.mark) =
      2 * q + 2 * s.length + rows.length * (4 * (w+1) + 4) + 5 := by
  have h : size (rows.map Dusk.mark) = rows.length * (4 * (w+1) + 4) + 1 := by
    induction rows with
    | nil => simp
    | cons a rows ih => simp only [List.map_cons, size_cons, Dusk.volume, ih,
        List.length_cons, Nat.succ_mul]; omega
  simp only [size_prod, size_tally, tally_length, size_word, h]
  omega

/-- One fixed tape program performs the whole scaled accumulation and final
shift in polynomially many physical transitions, restoring the other registers. -/
theorem shiftedRootWords_physical :
    ∃ C d : ℕ, ShortWord.PhysicalTask (fun x => C * (size x + 1)^d) send
      (fun x => send (shiftedRootWords x)) := by
  obtain ⟨t, ⟨d, C, ht⟩, run⟩ := shiftedRootWords_poly
  exact ⟨C, d, ShortWord.physicalTask (run.mono ht)⟩

/-- Truncation by `q` bits leaves the computed sum on the original root grid,
with absolute complex error bounded by two units in its last place. -/
theorem shiftedRootWords_error {w : ℕ} (p q : ℕ) (s : Word) (rows : List (Dusk.Grain w)) :
    ‖Grid.toC (Grid.content (shiftedRootWords (tally q, s, rows.map Dusk.mark))) / (2 : ℂ)^p -
      ((value s : ℂ) / 2^q) * (rows.map (Grid.meaning p w)).sum‖ ≤ (2 : ℝ) / 2^p := by
  rw [← scaledRootWords_meaning, shiftedRootWords, Grid.rest_r, pow_add, mul_comm ((2 : ℂ)^p),
    ← div_div, ← sub_div, norm_div, norm_pow, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  exact div_le_div_of_nonneg_right (Grid.embedded ..) (by positivity)

end FixedPoint

end NearSquareRoot
end Computability
end OAI
