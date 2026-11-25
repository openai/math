import OAI.Computability.NearSquareRoot.PrecisionGridQuantization
import OAI.Computability.IntegerMultiplication.Carry.Remainder

/-! # Downward-rounded reciprocal square roots on the integer multiplier's grid

For a positive axis length `a`, divide the integer square-root numerator at
fractional precision `p` by `a`. Both divisions round down, so the result is
exactly the floor of the target scaled by `2^p`. The setup program uses the
same binary words as the P192 square-root and Euclidean-division routines.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits

def invSqrtNumerator (a p : ℕ) : ℕ := sqrtNumerator a p / a

theorem invSqrtNumerator_interval {a : ℕ} (ha : 0 < a) (p : ℕ) :
    (invSqrtNumerator a p : ℝ) ≤ (Real.sqrt a)⁻¹ * (2 : ℝ) ^ p ∧
    (Real.sqrt a)⁻¹ * (2 : ℝ) ^ p < (invSqrtNumerator a p : ℝ) + 1 := by
  let q := invSqrtNumerator a p
  have h₁ : q * a ≤ sqrtNumerator a p := Nat.div_mul_le_self _ _
  have h₂ : sqrtNumerator a p + 1 ≤ (q + 1) * a := by
    have hrem := Nat.mod_lt (sqrtNumerator a p) ha
    have hsum := Nat.div_add_mod (sqrtNumerator a p) a
    change sqrtNumerator a p + 1 ≤ (sqrtNumerator a p / a + 1) * a
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm _ a]
    omega
  have hr₁ : (q : ℝ) * a ≤ sqrtNumerator a p := by exact_mod_cast h₁
  have hr₂ : (sqrtNumerator a p : ℝ) + 1 ≤ (q + 1 : ℝ) * a := by exact_mod_cast h₂
  have hr : 0 < (a : ℝ) := by exact_mod_cast ha
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 hr
  have cancel : (Real.sqrt a)⁻¹ * (a : ℝ) = Real.sqrt a := by
    calc
      _ = (Real.sqrt a)⁻¹ * (Real.sqrt a)^2 := congrArg _ (Real.sq_sqrt hr.le).symm
      _ = _ := by rw [pow_two, inv_mul_cancel_left₀ hs.ne']
  have swap : (Real.sqrt a)⁻¹ * (2 : ℝ)^p * a = Real.sqrt a * (2 : ℝ)^p := by
    rw [mul_right_comm, cancel]
  obtain ⟨hl, hu⟩ := sqrtNumerator_interval a p
  constructor
  · apply (mul_le_mul_iff_left₀ hr).mp
    rw [swap]
    exact hr₁.trans hl
  · apply (mul_lt_mul_iff_left₀ hr).mp
    rw [swap]
    exact hu.trans_le hr₂

/-- Absolute error below one unit in the last place on the reciprocal grid. -/
theorem invSqrtNumerator_error {a : ℕ} (ha : 0 < a) (p : ℕ) :
    |(invSqrtNumerator a p : ℝ) / (2 : ℝ)^p - (Real.sqrt a)⁻¹| < 1 / (2 : ℝ)^p := by
  have hp : 0 < (2 : ℝ)^p := by positivity
  obtain ⟨hl, hu⟩ := invSqrtNumerator_interval ha p
  rw [abs_of_nonpos (sub_nonpos.mpr ((div_le_iff₀ hp).2 hl)), neg_sub, sub_lt_iff_lt_add,
    ← add_div, lt_div_iff₀ hp]
  linarith

theorem invSqrtNumerator_le (a p : ℕ) : invSqrtNumerator a p ≤ 2 ^ p := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [invSqrtNumerator]
  have hs : 1 ≤ Real.sqrt a := (Real.one_le_sqrt).mpr (by exact_mod_cast ha)
  have h := (invSqrtNumerator_interval ha p).1
  have h' : (Real.sqrt a)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
  have hh : (invSqrtNumerator a p : ℝ) ≤ (2 : ℝ)^p :=
    h.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h' (by positivity : 0 ≤ (2 : ℝ)^p))
  exact_mod_cast hh

/-- Unary precision and binary positive axis length produce a little-endian
numerator padded to exactly `p+1` bits. Division by zero produces zero. -/
def invSqrtNumeratorWord (x : Tally × Word) : Word :=
  resize (() :: x.1, (Carry.nat_div (sqrtNumeratorWord x, x.2)).1)

theorem invSqrtNumeratorWord_poly : Poly invSqrtNumeratorWord := by
  have hd : Poly (fun x : Tally × Word => (Carry.nat_div (sqrtNumeratorWord x, x.2)).1) :=
    (sqrtNumeratorWord_poly.pair (show Poly (fun x : Tally × Word => x.2) by fun_prop)).compose
      Carry.polyND.fstCompose
  have ht : Easy (fun x : Tally × Word => () :: x.1) := by fun_prop
  exact (ht.poly.pair hd).compose ((easy_resize Easy.identity).poly)

theorem invSqrtNumeratorWord_spec (t : Tally) (s : Word) :
    (invSqrtNumeratorWord (t, s)).length = t.length + 1 ∧
    value (invSqrtNumeratorWord (t, s)) = invSqrtNumerator (value s) t.length := by
  have hw : tally (t.length + 1) = () :: t := by simpa using recover_tally (() :: t)
  unfold invSqrtNumeratorWord
  simp only
  rw [← hw]
  change (sized (t.length + 1) _).length = _ ∧ value (sized (t.length + 1) _) = _
  refine ⟨sized_length .., ?_⟩
  rw [sized_low, (Carry.division_rules ..).1, (sqrtNumeratorWord_spec t s).2]
  apply Nat.mod_eq_of_lt
  exact (invSqrtNumerator_le (value s) t.length).trans_lt (by
    rw [pow_succ]; have := Nat.two_pow_pos t.length; omega)

/-- Signed complex record for the real reciprocal normalization factor. -/
def invSqrtRecord (p w a : ℕ) : Dusk.Grain w := encodeNumerator w (invSqrtNumerator a p)

private theorem invSqrtNumerator_fits {p w : ℕ} (a : ℕ) (hw : p + 1 ≤ w) :
    invSqrtNumerator a p < 2^w := (invSqrtNumerator_le a p).trans_lt
  (Nat.pow_lt_pow_right (by decide) (by omega))

theorem invSqrtRecord_error {a p w : ℕ} (ha : 0 < a) (hw : p + 1 ≤ w) :
    ‖Grid.meaning p w (invSqrtRecord p w a) - ((Real.sqrt a)⁻¹ : ℝ)‖ < 1 / (2 : ℝ)^p := by
  rw [invSqrtRecord, meaning_encodeNumerator p (invSqrtNumerator_fits a hw)]
  have hc : ((invSqrtNumerator a p : ℝ) / 2 ^ p : ℝ) =
      ((invSqrtNumerator a p : ℂ) / 2 ^ p : ℂ) := by push_cast; rfl
  rw [← hc, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact invSqrtNumerator_error ha p

/-- P192 setup program packing the computed dyadic into its signed complex record. -/
def invSqrtRecordWord (x : Tally × Tally × Word) : Dusk.Pair :=
  encodeNumeratorWord (x.2.1, invSqrtNumeratorWord (x.1, x.2.2))

theorem invSqrtRecordWord_poly : Poly invSqrtRecordWord :=
  ((show Poly (fun x : Tally × Tally × Word => x.2.1) from by fun_prop).pair
    ((show Poly (fun x : Tally × Tally × Word => (x.1,x.2.2)) from by fun_prop).compose
      invSqrtNumeratorWord_poly)).compose encodeNumeratorWord_easy.poly

theorem invSqrtRecordWord_spec (p w : Tally) (s : Word) (hw : p.length + 1 ≤ w.length) :
    invSqrtRecordWord (p,w,s) = Dusk.mark (invSqrtRecord p.length w.length (value s)) := by
  have fit : value (invSqrtNumeratorWord (p,s)) < 2^w.length := by
    rw [(invSqrtNumeratorWord_spec p s).2]
    exact invSqrtNumerator_fits _ hw
  rw [invSqrtRecordWord, encodeNumeratorWord_spec _ _ fit, (invSqrtNumeratorWord_spec p s).2]
  simp [invSqrtRecord, encodeNumerator, Grid.wrapMap]

theorem invSqrtRecord_has {I : Type} {r : Strip.Regime I} {p w a : I → ℕ}
    (hp : Staff.Realizes r p) (hw : Staff.Realizes r w) (ha : Carry.Figure r a)
    (hwidth : ∀ i, p i + 1 ≤ w i) :
    r.Has (fun i => Dusk.mark (invSqrtRecord (p i) (w i) (a i))) := by
  obtain ⟨s, hsword, hval⟩ := ha
  have pword : r.Has (fun i => tally (p i)) := hp
  have wword : r.Has (fun i => tally (w i)) := hw
  have got := (pword.pair (wword.pair hsword)).thenDo invSqrtRecordWord_poly
  have spec i := invSqrtRecordWord_spec (tally (p i)) (tally (w i)) (s i)
    (by simpa only [tally_length] using hwidth i)
  have e (i : I) : invSqrtRecordWord (tally (p i), tally (w i), s i) =
      Dusk.mark (invSqrtRecord (p i) (w i) (a i)) := by
    rw [spec, tally_length, tally_length, hval]
  simpa only [e] using got

end FixedPoint

end NearSquareRoot
end Computability
end OAI
