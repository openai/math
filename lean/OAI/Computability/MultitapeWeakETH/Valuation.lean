import OAI.Computability.MultitapeWeakETH.FourColumns
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.Fin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! # The valuation penalty in the four-column argument -/

namespace OAI.Computability.MultitapeWeakETH

open scoped BigOperators

/-- Count zero bits starting at the low end of the word, capped at its width. -/
def trailing : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, x => if x%2 = 0 then trailing n (x/2) + 1 else 0

@[simp] theorem trailing_zero (n : ℕ) : trailing n 0 = n := by
  induction n <;> simp [trailing, *]

private theorem sum_pairs (f : ℕ → ℝ) (m : ℕ) :
    ∑ x ∈ Finset.range (2*m), f x =
      ∑ i ∈ Finset.range m, (f (2*i) + f (2*i+1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ,Finset.sum_range_succ,Finset.sum_range_succ,ih,Finset.sum_range_succ]
    ring

private theorem sum_trailing (n : ℕ) (a : ℝ) :
    ∑ x ∈ Finset.range (2^(n+1)), a^(trailing (n+1) x) =
      a * (∑ i ∈ Finset.range (2^n), a^(trailing n i)) + (2:ℝ)^n := by
  rw [pow_succ',sum_pairs]
  simp [trailing,pow_succ,Finset.sum_add_distrib,Finset.mul_sum,mul_comm]

/-- The moment is uniformly bounded in the width, including the all-zero residue.
The bound is the manuscript's K when a = 2^λ. -/
theorem trailing_moment (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (h₂ : a < 2) :
    (𝔼 x : Fin (2^n), a^(trailing n x.val)) ≤ 1 + 1/(2-a) := by
  rw [Fintype.expect_eq_sum_div_card,Fin.sum_univ_eq_sum_range (fun x => a^trailing n x),
    Fintype.card_fin,Nat.cast_pow,
    Nat.cast_ofNat]
  apply (div_le_iff₀ (by positivity)).mpr
  induction n with
  | zero =>
    have pos : 0 ≤ 1/(2-a) := by positivity
    simpa [trailing,sub_nonneg] using pos
  | succ n ih =>
    rw [sum_trailing,pow_succ]
    have inv := div_mul_cancel₀ (1:ℝ) (show 2-a ≠ 0 by linarith)
    have p : a * (1+1/(2-a)) + 1 ≤ 2 * (1+1/(2-a)) := by nlinarith
    nlinarith only [mul_le_mul_of_nonneg_left ih ha,
      mul_le_mul_of_nonneg_right p (show 0 ≤ (2:ℝ)^n by positivity)]

private theorem expect_pair {I J : Type*} [Fintype I] [Fintype J] (f : I × J → ℝ) :
    (𝔼 p, f p) = 𝔼 i, 𝔼 j, f (i,j) := by
  rw [← Finset.expect_product']
  simp

/-- Lemma 4.1 in multiplicative form. The four indicators in the expectation
count exactly the rows in the intersection. The ring of indices is modulo 2^n. -/
theorem exists_shifted_columns (n u : ℕ) {R : Type*} [Fintype R] [Nonempty R]
    (good : R → Fin (2^n) → Bool) {rate : ℝ} (hr : rate < 1) :
    let f (x : R) (y : Fin (2^n)) : ℝ := if good x y then 1 else 0
    let δ := 𝔼 x, 𝔼 y, f x y
    ∃ y z y' z' : Fin (2^n), y'-z' = 2^u*(y-z) ∧
      δ^4 * ((2:ℝ)^rate)^(trailing n (y-z).val) ≤
        (1 + 1/(2-(2:ℝ)^rate)) * (𝔼 x, (f x y * f x y') * (f x z * f x z')) := by
  intro f δ
  let G := Fin (2^n)
  let h (y : G) := (2^u : Fin (2^n))*y
  let a := (2:ℝ)^rate
  let w (v : G) := a^(trailing n v.val)
  let weight (p : G × G × G) := w (p.2.1-p.2.2)
  let q (p : G × G × G) := 𝔼 x,
    (f x p.2.1 * f x (h p.2.1-p.1)) * (f x p.2.2 * f x (h p.2.2-p.1))
  have mass : δ^4 ≤ 𝔼 p, q p := by
    simpa only [expect_pair,q,δ] using four_columns_mean f h
  have wp : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
  have weakMoment := trailing_moment n wp.le
    (show a < 2 by simpa [a] using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hr)
  have budget : (𝔼 p, weight p) ≤ 1+1/(2-a) := by
    have shift (y : G) : (𝔼 z : G, w (y-z)) = 𝔼 v : G, w v :=
      Fintype.expect_equiv (Equiv.subLeft y) _ w (fun _ => rfl)
    simpa only [expect_pair,weight,shift,Fintype.expect_const] using weakMoment
  obtain ⟨⟨t,y,z⟩,bound⟩ := exists_four_columns_weighted q weight mass budget
    (fun p => pow_pos wp _) (fun p => Finset.expect_nonneg fun x _ => by dsimp [f]; positivity)
  exact ⟨y,z,h y-t,h z-t,by rw [sub_sub_sub_cancel_right,mul_sub],bound⟩

end OAI.Computability.MultitapeWeakETH
