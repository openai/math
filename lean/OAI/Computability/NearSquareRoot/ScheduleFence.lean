import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic

/-!
# Digit products inside a common space fence

The uniform multiplier splits each operand into a power-of-two number of
chunks before running a candidate on a pair of chunks. Padding is independent
of the values of the operands, so these estimates also apply to inputs with
leading zeros.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform

/-- The common width of the `r` chunks of an `n`-bit operand. -/
def chunkWidth (n r : ℕ) : ℕ := n ⌈/⌉ r

theorem chunkWidth_bounds {n r : ℕ} (hr : 0 < r) :
    n ≤ r * chunkWidth n r ∧ r * chunkWidth n r < n + r := by
  constructor
  · exact (ceilDiv_le_iff_le_mul hr).1 le_rfl
  · unfold chunkWidth
    rw [Nat.ceilDiv_eq_add_pred_div, mul_comm]
    have := Nat.div_mul_le_self (n + r - 1) r
    omega

/-- Even unsuccessful attempts need at most `4*n` bits for the accumulator. -/
theorem accumulator_width_le {n r : ℕ} (hr : 0 < r) (hrn : r ≤ n) :
    2 * (r * chunkWidth n r) ≤ 4 * n := by
  have := (chunkWidth_bounds (n := n) hr).2
  omega

/-- A fixed split preserves every eventual lower cutoff for the candidate
once the total length is at least the split count times that cutoff. -/
theorem cutoff_le_chunkWidth {m n r : ℕ} (hr : 0 < r) (hm : r * m ≤ n) :
    m ≤ chunkWidth n r :=
  Nat.le_of_mul_le_mul_left (hm.trans (chunkWidth_bounds hr).1) hr

/-- If one digit product costs at most `u * F u`, the sum over all
`r²` pairs is bounded by a constant times the unsplit cost for fixed `r`. -/
theorem digit_products_cost_le {n r : ℕ} (hr : 0 < r) (hrn : r ≤ n)
    {F : ℕ → ℝ} (hF : Monotone F) (hzero : 0 ≤ F n) :
    (r : ℝ) ^ 2 * chunkWidth n r * F (chunkWidth n r) ≤
      2 * r * n * F n := by
  have hu : chunkWidth n r ≤ n :=
    (ceilDiv_le_iff_le_mul hr).2 (Nat.le_mul_of_pos_left n hr)
  have hru : r * chunkWidth n r ≤ 2 * n := by
    have := (chunkWidth_bounds (n := n) hr).2
    omega
  have hcast : (r : ℝ) * chunkWidth n r ≤ 2 * n := by exact_mod_cast hru
  calc
    _ ≤ (r : ℝ) ^ 2 * chunkWidth n r * F n :=
      mul_le_mul_of_nonneg_left (hF hu) (by positivity)
    _ = (r : ℝ) * ((r : ℝ) * chunkWidth n r) * F n := by ring
    _ ≤ (r : ℝ) * (2 * n) * F n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcast (by positivity)) hzero
    _ = _ := by ring

/-- If a candidate needs at most `c*(u+1)` cells on `u`-bit operands,
one fixed split fits in the same `n`-cell fence at every large length. -/
theorem chunkWidth_fits {c n r : ℕ} (hr : 0 < r) (hc : 2 * c ≤ r)
    (hn : 2 * r ≤ n) : c * (chunkWidth n r + 1) ≤ n := by
  have hpad := (chunkWidth_bounds (n := n) hr).2
  have h := Nat.mul_le_mul_right (chunkWidth n r + 1) hc
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_add, Nat.mul_one] at h
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- Every candidate with a linear space constant has a permissible dyadic split. -/
theorem exists_dyadic_split (c : ℕ) :
    ∃ k : ℕ, ∀ n ≥ 2 * 2 ^ k,
      2 ^ k ≤ n ∧ c * (chunkWidth n (2 ^ k) + 1) ≤ n := by
  refine ⟨2 * c, fun n hn => ⟨by omega, ?_⟩⟩
  exact chunkWidth_fits (by positivity) (Nat.le_of_lt (Nat.lt_two_pow_self)) hn

/-- Extract chunk number `i` counting from the least significant end. The
digits absent on the left of a short operand are exactly zero. -/
def chunkDigit (b x i : ℕ) : ℕ := x / b ^ i % b

theorem chunkDigit_lt {b : ℕ} (hb : 0 < b) (x i : ℕ) : chunkDigit b x i < b :=
  Nat.mod_lt _ hb

private theorem chunkExpansion (b x r : ℕ) :
    (∑ i ∈ Finset.range r, chunkDigit b x i * b ^ i) + x / b ^ r * b ^ r = x := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, pow_succ, ← Nat.div_div_eq_div_mul]
    unfold chunkDigit
    calc
      _ = (∑ i ∈ Finset.range r, x / b ^ i % b * b ^ i) +
          (x / b ^ r % b + b * (x / b ^ r / b)) * b ^ r := by ring
      _ = x := by rw [Nat.mod_add_div]; exact ih

theorem sum_chunkDigits {b x r : ℕ} (hx : x < b ^ r) :
    ∑ i ∈ Finset.range r, chunkDigit b x i * b ^ i = x := by
  simpa [Nat.div_eq_of_lt hx] using chunkExpansion b x r

/-- The exact value added to the accumulator by all the shifted digit products. -/
theorem sum_shifted_products {b x y r : ℕ} (hx : x < b ^ r) (hy : y < b ^ r) :
    ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r,
      chunkDigit b x i * chunkDigit b y j * b ^ (i + j) = x * y := by
  calc
    _ = (∑ i ∈ Finset.range r, chunkDigit b x i * b ^ i) *
        (∑ j ∈ Finset.range r, chunkDigit b y j * b ^ j) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add]
      ring
    _ = _ := by rw [sum_chunkDigits hx, sum_chunkDigits hy]

/-- The dyadic padded expansion computes the original product. Its magnitude
fits even in the original unpadded `2*n` output positions. -/
theorem padded_product {n r x y : ℕ} (hr : 0 < r) (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    let b := 2 ^ chunkWidth n r
    (∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r,
        chunkDigit b x i * chunkDigit b y j * b ^ (i+j)) = x * y ∧
      x * y < 2 ^ (2 * n) := by
  dsimp only
  have hpow : 2 ^ n ≤ (2 ^ chunkWidth n r) ^ r := by
    rw [← pow_mul, Nat.mul_comm (chunkWidth n r)]
    exact Nat.pow_le_pow_right (by decide) (chunkWidth_bounds hr).1
  refine ⟨sum_shifted_products (hx.trans_le hpow) (hy.trans_le hpow), ?_⟩
  rw [two_mul, pow_add]
  calc x * y ≤ x * 2 ^ n := Nat.mul_le_mul_left _ hy.le
       _ < 2 ^ n * 2 ^ n := Nat.mul_lt_mul_of_pos_right hx (by positivity)

/-- In any order of visiting the digit pairs, every partial accumulator has
the same `2*n`-bit cap as the final product. -/
theorem partial_accumulator_lt {n r x y : ℕ} (hr : 0 < r)
    (hx : x < 2 ^ n) (hy : y < 2 ^ n) {visited : Finset (ℕ × ℕ)}
    (hsub : visited ⊆ (Finset.range r).product (Finset.range r)) :
    let b := 2 ^ chunkWidth n r
    ∑ p ∈ visited, chunkDigit b x p.1 * chunkDigit b y p.2 * b ^ (p.1 + p.2) <
      2 ^ (2 * n) := by
  let b := 2 ^ chunkWidth n r
  let term := fun p : ℕ × ℕ => chunkDigit b x p.1 * chunkDigit b y p.2 * b ^ (p.1 + p.2)
  obtain ⟨hfull, hbound⟩ := padded_product hr hx hy
  change (∑ p ∈ visited, term p) < _
  apply lt_of_le_of_lt (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _))
  change (∑ p ∈ Finset.range r ×ˢ Finset.range r, term p) < _
  rw [Finset.sum_product]
  exact hfull.trans_lt hbound

end Uniform

end NearSquareRoot
end Computability
end OAI
