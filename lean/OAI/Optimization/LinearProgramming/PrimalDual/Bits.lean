import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import OAI.Optimization.LinearProgramming.RAM.Basic
import OAI.Optimization.LinearProgramming.PrimalDual.Matrix

/-! Encoding lengths of the intermediate dot products and normalizations in §2.
The register encoding is `RAM.ratBits`, with the reduced signed numerator and
positive denominator. The bounds apply to every partial sum, in any order. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open scoped BigOperators
open OAI.Optimization.LinearProgramming.RAM

private def height (q : ℚ) : ℕ := max q.num.natAbs q.den
private def width (q : ℚ) : ℕ := (height q).log2 + 1

private theorem height_pos (q : ℚ) : 0 < height q :=
  q.pos.trans_le (le_max_right _ _)

private theorem log2_mono {x y : ℕ} (h : x ≤ y) : x.log2 ≤ y.log2 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · exact Nat.lt_succ_iff.mp <| (Nat.log2_lt hx.ne').2 (h.trans_lt Nat.lt_log2_self)

private theorem width_le_ratBits (q : ℚ) : width q ≤ ratBits q := by
  rcases le_total q.num.natAbs q.den with h | h
  · simp only [width, height, max_eq_right h, ratBits]; omega
  · simp only [width, height, max_eq_left h, ratBits]; omega

private theorem ratBits_le_width (q : ℚ) : ratBits q ≤ 1 + 2 * width q := by
  have hn := log2_mono (le_max_left q.num.natAbs q.den)
  have hd := log2_mono (le_max_right q.num.natAbs q.den)
  unfold ratBits width height
  omega

private theorem height_mul (q r : ℚ) : height (q*r) ≤ height q * height r := by
  apply max_le
  · rw [Rat.mul_num]
    exact (Int.natAbs_ediv_le_natAbs _ _).trans <| by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (le_max_left _ _) (le_max_left _ _)
  · exact (Nat.le_of_dvd (Nat.mul_pos q.pos r.pos) (Rat.mul_den_dvd q r)).trans
      (Nat.mul_le_mul (le_max_right _ _) (le_max_right _ _))

private theorem height_add (q r : ℚ) : height (q+r) ≤ 2 * (height q * height r) := by
  apply max_le
  · rw [Rat.num_add]
    refine (Int.natAbs_ediv_le_natAbs _ _).trans <| (Int.natAbs_add_le _ _).trans ?_
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    have h1 := Nat.mul_le_mul (le_max_left q.num.natAbs q.den) (le_max_right r.num.natAbs r.den)
    have h2 := Nat.mul_le_mul (le_max_right q.num.natAbs q.den) (le_max_left r.num.natAbs r.den)
    unfold height
    rw [Nat.mul_comm r.num.natAbs q.den]
    omega
  · have h := (Nat.le_of_dvd (Nat.mul_pos q.pos r.pos) (Rat.add_den_dvd q r)).trans
      (Nat.mul_le_mul (le_max_right q.num.natAbs q.den) (le_max_right r.num.natAbs r.den))
    unfold height
    omega

private theorem height_product_lt (q r : ℚ) : height q * height r < 2 ^ (width q + width r) := by
  rw [pow_add]
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.lt_log2_self (n := height r)).le)
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_log2_self (n := height q)) (by positivity))

private theorem width_mul (q r : ℚ) : width (q*r) ≤ width q + width r :=
  Nat.succ_le_of_lt <| (Nat.log2_lt (height_pos _).ne').2
    ((height_mul _ _).trans_lt (height_product_lt _ _))

private theorem width_add (q r : ℚ) : width (q+r) ≤ width q + width r + 1 := by
  apply Nat.succ_le_of_lt
  apply (Nat.log2_lt (height_pos _).ne').2
  refine (height_add _ _).trans_lt ?_
  rw [pow_succ, Nat.mul_comm _ 2]
  exact Nat.mul_lt_mul_of_pos_left (height_product_lt _ _) (by decide)

private theorem width_inv (q : ℚ) : width q⁻¹ = width q := by
  by_cases h : q.num = 0
  · rw [Rat.zero_of_num_zero h, inv_zero]
  · simp [width, height, Rat.den_inv, h, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero h, max_comm]

private theorem width_neg (q : ℚ) : width (-q) = width q := by simp [width, height]

theorem ratBits_neg (q : ℚ) : ratBits (-q) = ratBits q := by simp [ratBits]

/-- In particular, taking a nonzero reciprocal preserves a linear bound on bit length. -/
theorem ratBits_inv_le (q : ℚ) : ratBits q⁻¹ ≤ 1 + 2 * ratBits q := by
  have h := ratBits_le_width q⁻¹
  rw [width_inv] at h
  linarith [width_le_ratBits q]

/-- Arithmetic in the final primal/dual decoding has a linear bit bound per product. -/
theorem ratBits_mul_le (q r : ℚ) : ratBits (q*r) ≤ 1 + 2 * (ratBits q + ratBits r) := by
  linarith [ratBits_le_width (q*r), width_mul q r, width_le_ratBits q, width_le_ratBits r]

theorem ratBits_sub_le (q r : ℚ) : ratBits (q-r) ≤ 3 + 2 * (ratBits q + ratBits r) := by
  rw [sub_eq_add_neg]
  have h := width_add q (-r)
  rw [width_neg] at h
  linarith [ratBits_le_width (q + -r), width_le_ratBits q, width_le_ratBits r]

/-- A binary encoding bound for every partial dot product. The sum on the right
accounts for the entries actually used, including the products and all additions. -/
theorem ratBits_partial_dot_le {ι : Type*} (t : Finset ι) (a b : ι → ℚ) :
    ratBits (∑ i ∈ t, a i * b i) ≤ 3 + 2 * ∑ i ∈ t, (ratBits (a i) + ratBits (b i) + 1) := by
  classical
  have h : width (∑ i ∈ t, a i * b i) ≤ 1 + ∑ i ∈ t, (ratBits (a i) + ratBits (b i) + 1) := by
    induction t using Finset.induction_on with
    | empty => simp [width, height]; rfl
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (width_add _ _).trans <| by
        linarith [width_mul (a i) (b i), width_le_ratBits (a i), width_le_ratBits (b i)]
  linarith [ratBits_le_width (∑ i ∈ t, a i * b i)]

/-- All coefficients in the second call fit the same register bound as the input. -/
theorem ratBits_jointMatrix_le {I J : Type*} [DecidableEq I] (A : Matrix I J ℚ) (b : I → ℚ)
    (c : J → ℚ) {B : ℕ} (h0 : 3 ≤ B) (ha : ∀ i j, ratBits (A i j) ≤ B)
    (hb : ∀ i, ratBits (b i) ≤ B) (hc : ∀ j, ratBits (c j) ≤ B)
    (i : JointRow I J) (j : J ⊕ I) : ratBits (jointMatrix A b c i j) ≤ B := by
  have hz : ratBits 0 ≤ B := h0
  have hn : ratBits (-1) ≤ B := h0
  rcases i with i | i | i | i | _ <;> rcases j with j | j <;>
    simp [jointMatrix, ratBits_neg, *]
  split <;> assumption

/-- Encoding lengths in the right-hand side of the second call. -/
theorem ratBits_jointRhs_le {I J : Type*} (b : I → ℚ) (c : J → ℚ)
    {B : ℕ} (h0 : 3 ≤ B) (hb : ∀ i, ratBits (b i) ≤ B) (hc : ∀ j, ratBits (c j) ≤ B)
    (i : JointRow I J) : ratBits (jointRhs b c i) ≤ B := by
  have hz : ratBits 0 ≤ B := h0
  rcases i with i | i | i | i | _ <;> simp [jointRhs, ratBits_neg, *]

/-- Normalizing a ray or certificate multiplies every entry by one reciprocal. -/
theorem ratBits_normalized_le (s r : ℚ) : ratBits (s⁻¹ * r) ≤ 3 + 4 * ratBits s + 2 * ratBits r := by
  linarith [ratBits_inv_le s, ratBits_mul_le s⁻¹ r]

end PrimalDual
end LinearProgramming
end Optimization
end OAI
