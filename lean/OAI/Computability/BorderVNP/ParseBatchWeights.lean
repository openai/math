import OAI.Computability.BorderVNP.ParseTable
import Mathlib.Data.Nat.Log

/-! # Binary parameter factors for a batch of coefficient queries

In Lemma 2.3 each parameter has one unary factor per count bit for the entire
batch. Sorting and checking the records must preserve the multiplicities in the
sum below. No parameter value is copied once per occurrence.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatch

open MvPolynomial VPVNP VPVNP.ParseGrammar
open scoped Classical

/-- The contribution of the low `w` bits of a natural number to its binary value. -/
private theorem low_sum (a w : ℕ) :
    (∑ j ∈ Finset.range w, if a.testBit j then 2 ^ j else 0) = a % 2^w := by
  induction w with
  | zero => simp [Nat.mod_one]
  | succ w ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have expand := Nat.mod_add_div (a % (2^w * 2)) (2^w)
    rw [Nat.mod_mod_of_dvd _ (dvd_mul_right _ _), Nat.mod_mul_right_div_self] at expand
    have bound := Nat.mod_lt (a / 2^w) (by decide : 0 < 2)
    rw [Nat.testBit_eq_decide_div_mod_eq]
    by_cases he : a / 2^w % 2 = 1
    · simpa [he] using expand
    · have hz : a / 2^w % 2 = 0 := by omega
      simpa [hz] using expand

/-- The product of unary weights for a fixed parameter reads exactly its count. -/
theorem prod_unary {R : Type*} [CommMonoid R] (z : R) {w a : ℕ} (ha : a < 2 ^ w) :
    (∏ j : Fin w, if a.testBit j.val then z ^ (2 ^ j.val) else 1) = z ^ a := by
  rw [Fin.prod_univ_eq_prod_range (fun j => if a.testBit j then z ^ (2^j) else 1)]
  convert (Finset.prod_pow_eq_pow_sum (Finset.range w)
    (fun j => if a.testBit j then 2^j else 0) z) using 1
  · apply Finset.prod_congr rfl
    intro j _
    split <;> simp
  · rw [low_sum, Nat.mod_eq_of_lt ha]

variable {H : Type*} [Fintype H] {m n r : ℕ}

/-- Histogram of the parameter uses in the whole ordered batch. -/
noncomputable def counts (d : Fin n) (h : H) (x : Fin r → Fin m → Bool)
    (p : ∀ i, ParseChoice H d (x i)) : GrammarLabel (Fin m × Bool) H n →₀ ℕ :=
  ∑ i, histogram d h (p i).1

/-- No count exceeds the total number of parse nodes in the batch. -/
theorem count_le (d : Fin n) (h : H) (x : Fin r → Fin m → Bool)
    (p : ∀ i, ParseChoice H d (x i)) (j : GrammarLabel (Fin m × Bool) H n) :
    counts d h x p j ≤ r * (2*d.val + 1) := by
  classical
  rw [counts, Finsupp.finsetSum_apply]
  calc
    _ ≤ ∑ _ : Fin r, (2*d.val + 1) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← histogram_sum d h (p i).1]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ = _ := by simp

/-- Multiplying full-batch query polynomials and expanding gives one monomial for each
ordered tuple of valid parses, with its original multiplicity. -/
theorem product_eq_sum (d : Fin n) (h : H) (x : Fin r → Fin m → Bool) :
    (∏ i, labelQuery d h (x i)) =
      ∑ p : ∀ i, ParseChoice H d (x i), monomial (counts d h x p) (1 : ℤ) := by
  classical
  simp only [labelQuery_eq_sum_histogram, Fintype.prod_sum, counts, monomial_sum_one]

/-- Lemma 2.3's parameter weights: each pair of a parameter and count bit appears at a
single fixed position, irrespective of how many occurrences chose that parameter. -/
theorem product_eq_binary_weights (d : Fin n) (h : H) (x : Fin r → Fin m → Bool) :
    let w := Nat.clog 2 (r * (2*d.val + 1) + 1)
    (∏ i, labelQuery d h (x i)) =
      ∑ p : ∀ i, ParseChoice H d (x i), ∏ j : GrammarLabel (Fin m × Bool) H n, ∏ b : Fin w,
        if (counts d h x p j).testBit b.val then
          (X j : MvPolynomial _ ℤ) ^ (2 ^ b.val) else 1 := by
  classical
  dsimp only
  rw [product_eq_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [monic_monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  refine Finset.prod_congr rfl fun j _ => (prod_unary _ ?_).symm
  exact (Nat.lt_succ_of_le (count_le d h x p j)).trans_le (Nat.le_pow_clog (by decide) _)

end ParseBatch

end BorderVNP
end Computability
end OAI
