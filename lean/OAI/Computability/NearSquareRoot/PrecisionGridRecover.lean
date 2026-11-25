import OAI.Computability.IntegerMultiplication.Grid.Value
import OAI.Computability.IntegerMultiplication.Ask.Broadcast

/-! # Reading integral coefficients out of fixed-point records

The signed-magnitude calculation adds a dyadic offset to twice the magnitude
and drops the low bits. This works at zero fractional precision too.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits

private def roundedWord (i : Tally × Word) : Word :=
  let numer := Bits.add (false :: i.2, fill false i.1 ++ [true])
  (cutLists (() :: i.1, numer)).2

private theorem roundedWord_easy : Easy roundedWord := by
  unfold roundedWord
  apply Easy.sndCompose
  apply easy_cut
  fun_prop

private theorem value_drop (p : ℕ) (w : Word) :
    value (w.drop p) = value w / 2 ^ p := by
  induction p generalizing w with
  | zero => simp
  | succ p ih =>
    cases w with
    | nil => simp
    | cons b w =>
      change value (w.drop p) = _
      simp only [pow_succ', ← Nat.div_div_eq_div_mul, value_half, ih]

private theorem roundedWord_value (p : ℕ) (w : Word) :
    value (roundedWord (tally p, w)) = (2 * value w + 2 ^ p) / 2 ^ (p+1) := by
  simp [roundedWord, cutLists, value_drop, add_val, value_append, fill_eq]

private theorem roundedWord_length (p : ℕ) (w : Word) :
    (roundedWord (tally p, w)).length = w.length + 2 := by
  simp [roundedWord, cutLists, fill_eq]
  omega

private theorem roundedMagnitude_eq (m p : ℕ) (z : ℤ)
    (h : |(m : ℝ) / (2 : ℝ)^p - (z : ℝ)| < 1/2) :
    (((2*m + 2^p) / (2^(p+1)) : ℕ) : ℤ) = z := by
  have hp : 0 < (2 : ℝ)^p := by positivity
  obtain ⟨hl, hu⟩ := abs_lt.mp h
  have hlo : ((z : ℝ) - 1/2) * 2^p < m :=
    (lt_div_iff₀ hp).mp (by linarith)
  have hhi : (m : ℝ) < ((z : ℝ) + 1/2) * 2^p :=
    (div_lt_iff₀ hp).mp (by linarith)
  have hlo' : (z : ℝ) * 2^(p+1) ≤ 2*m + 2^p := by
    rw [pow_succ]; linarith
  have hhi' : (2 : ℝ)*m + 2^p < ((z : ℝ)+1)*2^(p+1) := by
    rw [pow_succ]; linarith
  rw [Int.natCast_ediv]
  have hd : 0 < ((2^(p+1) : ℕ) : ℤ) := by positivity
  have hl' : z ≤ ((2*m + 2^p : ℕ) : ℤ) / (2^(p+1) : ℕ) :=
    (Int.le_ediv_iff_mul_le hd).mpr (by exact_mod_cast hlo')
  have hu' : ((2*m + 2^p : ℕ) : ℤ) / (2^(p+1) : ℕ) < z+1 :=
    (Int.ediv_lt_iff_lt_mul hd).mpr (by exact_mod_cast hhi')
  omega

/-- Decode the real coordinate, round its magnitude and retain its sign. -/
def readCoefficient (i : Tally × Dusk.Pair) : Grid.S :=
  let x := Grid.pull i.2.1
  (x.1, roundedWord (i.1, x.2))

/-- The coefficient reader is a single stack program with a linear time bound
in the size of the marked record and its fractional-bit ruler. -/
theorem readCoefficient_easy : Easy readCoefficient := by
  have hp : Easy (fun i : Tally × Dusk.Pair => Grid.pull i.2.1) := by fun_prop
  unfold readCoefficient
  exact hp.fstCompose.pair ((Easy.fst.pair hp.sndCompose).compose roundedWord_easy)

private theorem roundedSigned_exact (p : ℕ) (x : Grid.S) (z : ℤ)
    (h : |(Grid.whole x : ℝ) / (2 : ℝ)^p - (z : ℝ)| < 1/2) :
    Grid.whole (x.1, roundedWord (tally p, x.2)) = z := by
  obtain ⟨b,w⟩ := x
  cases b with
  | false =>
    simp [Grid.whole, Grid.tag] at h ⊢
    rw [roundedWord_value]
    exact roundedMagnitude_eq _ _ _ (by simpa only [one_div] using h)
  | true =>
    simp [Grid.whole, Grid.tag] at h ⊢
    have h' : |(value w : ℝ) / (2 : ℝ)^p - ((-z : ℤ) : ℝ)| < 1/2 := by
      rw [Int.cast_neg]
      rw [← abs_neg ((value w : ℝ) / (2 : ℝ)^p - -(z : ℝ))]
      convert h using 2 <;> ring
    rw [roundedWord_value, roundedMagnitude_eq _ _ (-z) h', neg_neg]

/-- A marked record within half a unit of an integer in its real coordinate
decodes to that integer, including when the coefficient is negative. -/
theorem readCoefficient_eq {p k : ℕ} (x : Dusk.Grain k) (z : ℤ)
    (h : |(Grid.meaning p k x).re - (z : ℝ)| < 1/2) :
    Grid.whole (readCoefficient (tally p, Dusk.mark x)) = z := by
  apply roundedSigned_exact
  have hre : (Grid.meaning p k x).re = ((Grid.aspect x).re : ℝ) / (2 : ℝ)^p := by
    unfold Grid.meaning
    rw [show (2 : ℂ)^p = Complex.ofReal ((2 : ℝ)^p) by push_cast; rfl, Complex.div_ofReal_re]
    simp [Grid.toC]
  simpa only [hre, Dusk.mark, Grid.lifted, Grid.aspect] using h

/-- The magnitude word that proceeds to the carries has the exact
nonnegative coefficient and a width independent of the fractional precision. -/
theorem readCoefficient_nat {p k : ℕ} (x : Dusk.Grain k) (n : ℕ)
    (h : |(Grid.meaning p k x).re - (n : ℝ)| < 1/2) :
    let w := (readCoefficient (tally p, Dusk.mark x)).2
    value w = n ∧ w.length = k + 3 := by
  obtain he := readCoefficient_eq x (n : ℤ) (by exact_mod_cast h)
  constructor
  · rw [← Grid.normal, he]
    simp
  · change (roundedWord (tally p, (Grid.pull (Dusk.trip x.re)).2)).length = _
    rw [roundedWord_length, show (Grid.pull (Dusk.trip x.re)).2.length = k+1 from Grid.pull_len _]

/-- Produce exactly the requested number of little-endian coefficient bits.
The two rulers specify the fractional precision and the output width. -/
def readCoefficientWord (i : Dusk.Pair × (Tally × Tally)) : Word :=
  Bits.resize (i.2.2, (readCoefficient (i.2.1, i.1)).2)

theorem readCoefficientWord_easy : Easy readCoefficientWord := by
  have hr := readCoefficient_easy
  unfold readCoefficientWord
  fun_prop

theorem readCoefficientWord_spec {p k b : ℕ} (x : Dusk.Grain k) (n : ℕ)
    (hn : n < 2^b) (h : |(Grid.meaning p k x).re - (n : ℝ)| < 1/2) :
    let w := readCoefficientWord (Dusk.mark x, tally p, tally b)
    w.length = b ∧ value w = n := by
  exact ⟨sized_length _ _, by
    change value (sized b _) = n
    rw [sized_low, (readCoefficient_nat x n h).1, Nat.mod_eq_of_lt hn]⟩

/-- Euclidean error estimates supply a complex absolute error per coordinate;
projection onto the real coordinate preserves the strict half-unit margin. -/
theorem readCoefficientWord_of_norm {p k b : ℕ} (x : Dusk.Grain k) (n : ℕ)
    (hn : n < 2^b) (h : ‖Grid.meaning p k x - (n : ℂ)‖ < 1/2) :
    let w := readCoefficientWord (Dusk.mark x, tally p, tally b)
    w.length = b ∧ value w = n := by
  apply readCoefficientWord_spec x n hn
  simpa only [Complex.sub_re, Complex.natCast_re] using (Complex.abs_re_le_norm _).trans_lt h

/-- Encoded size of a stream of marked complex records. -/
theorem markedListSize {k : ℕ} (s : List (Dusk.Grain k)) :
    size (s.map Dusk.mark) = s.length * (4*(k+1)+4) + 1 := by
  induction s with
  | nil => simp
  | cons x s ih =>
    simp only [List.map_cons, size_cons, Dusk.volume, ih, List.length_cons, Nat.succ_mul]
    omega

/-- Broadcast one pair of rulers across a whole stream. This linear charge
includes copying the parameters and traversing and rounding every record. -/
theorem readCoefficientStream {I : Type} {J : I → Type}
    (s : (i : I) → Strip.Series (J i)) (k p b : I → ℕ)
    (x : (i : I) → J i → Dusk.Grain (k i)) :
    let cost := fun i => ((s i).count + 1 : ℝ) * ((k i + p i + b i : ℕ) + 1 : ℝ)
    Carries cost
      (fun i => Tree.fork (send (tally (p i), tally (b i)))
        (Loom.strip (s i) (fun j => Dusk.mark (x i j))))
      (fun i => Loom.strip (s i) (fun j =>
        readCoefficientWord (Dusk.mark (x i j), tally (p i), tally (b i)))) := by
  let W := fun i => k i + p i + b i
  let hdr := fun i => (tally (p i), tally (b i))
  let row := fun i j => Dusk.mark (x i j)
  have hr : ∀ i j, size (row i j) ≤ 8 * (W i + 1) := by
    intro i j
    simp only [row, Dusk.volume, W]
    omega
  have hh : ∀ i, size (hdr i) ≤ 3 * (W i + 1) := by
    intro i
    simp only [hdr, size_prod, size_tally, tally_length, W]
    omega
  have oneRecord : Carries (fun i : Sigma J => ((W i.1 : ℝ) + 1)*1)
      (fun i => send (row i.1 i.2, hdr i.1))
      (fun i => send (readCoefficientWord (row i.1 i.2, hdr i.1))) := by
    apply Carries.func (y := fun i : Sigma J => (row i.1 i.2, hdr i.1))
    · intro i
      simp
    · refine ⟨12, fun i => ?_⟩
      change (size (row i.1 i.2, hdr i.1) : ℝ) ≤ _
      simp only [mul_one]
      exact_mod_cast (show size (row i.1 i.2, hdr i.1) ≤ 12*(W i.1 + 1) by
        change size (row i.1 i.2) + size (hdr i.1) + 1 ≤ _
        have := hr i.1 i.2
        have := hh i.1
        omega)
    · exact readCoefficientWord_easy
  simpa only [mul_one] using Ask.weight (w := W) (f := fun _ => 1) s row hdr
    (fun _ => readCoefficientWord) ⟨8, hr⟩ ⟨3, hh⟩ oneRecord (fun _ => le_rfl)


/-- A single stack command reads a natural-order array and leaves the list of
width-limited words consumed by the carry pass. Its time bound is the number
of records times their combined record and ruler widths. -/
theorem readCoefficientList {I : Type} (m k p b : I → ℕ)
    (x : (i : I) → Fin (m i) → Dusk.Grain (k i)) :
    Task (fun i => (m i + 1) * (k i + p i + b i + 1))
      (fun i => send ((tally (p i), tally (b i)), List.ofFn (fun j => Dusk.mark (x i j))))
      (fun i => send (List.ofFn (fun j =>
        readCoefficientWord (Dusk.mark (x i j), tally (p i), tally (b i))))) := by
  have h := (readCoefficientStream (fun i => Strip.Series.natural (m i)) k p b x).runs.release
  have hs {A : Type} [Codec A] {n : ℕ} (f : Fin n → A) :
      Loom.strip (Strip.Series.natural n) f = send (List.ofFn f) := by
    unfold Loom.strip
    rw [Strip.stripe_eq']
    change send (List.map _ (List.finRange _)) = _
    simp [List.finRange, Function.comp_def]
  refine h.conform (fun i => ?_) (fun i => ?_) (fun i => ?_)
  · simp only [Strip.Series.count_natural, ← Nat.cast_one (R := ℝ),
      ← Nat.cast_add, ← Nat.cast_mul, Nat.ceil_natCast]
  · rw [hs]
    rfl
  · exact hs _

end FixedPoint

end NearSquareRoot
end Computability
end OAI
