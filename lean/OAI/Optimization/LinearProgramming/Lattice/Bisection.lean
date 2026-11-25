import Mathlib.Tactic

/-! Dyadic approximation of a ratio of integer linear forms from sign queries (Appendix A). -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

/-- An integer query is evaluated against the hidden, real input vector. -/
def formValue {p : ℕ} (a : Fin p → ℤ) (v : Fin p → ℝ) : ℝ := ∑ i, (a i : ℝ) * v i

/-- The query compares `a(v)/b(v)` with `n/2^k`, when `b(v)` is positive. -/
def dyadicQuery {p : ℕ} (a b : Fin p → ℤ) (k : ℕ) (n : ℤ) : Fin p → ℤ :=
  fun i ↦ 2 ^ k * a i - n * b i

theorem dyadicQuery_value {p : ℕ} (a b : Fin p → ℤ) (v : Fin p → ℝ) (k : ℕ) (n : ℤ) :
    formValue (dyadicQuery a b k n) v = (2 : ℝ) ^ k * formValue a v - n * formValue b v := by
  simp only [formValue, dyadicQuery, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The numerator of the final dyadic midpoint, with the queries in reverse chronological order. -/
structure DyadicSearchResult (p : ℕ) where
  numerator : ℤ
  queries : List (Fin p → ℤ)

/-- One sign call per refinement, with `true` denoting a nonnegative integer linear form. -/
def dyadicSearch {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (a b : Fin p → ℤ) :
    ℕ → DyadicSearchResult p
  | 0 => ⟨0, []⟩
  | k + 1 =>
    let prev := dyadicSearch oracle a b k
    let query := dyadicQuery a b k prev.numerator
    ⟨2 * prev.numerator + (if oracle query then 1 else -1), query :: prev.queries⟩

theorem dyadicSearch_query_count {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (a b : Fin p → ℤ)
    (k : ℕ) : (dyadicSearch oracle a b k).queries.length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [dyadicSearch, ih]

theorem dyadicSearch_numerator_lt {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (a b : Fin p → ℤ)
    (k : ℕ) : |(dyadicSearch oracle a b k).numerator| < (2 : ℤ) ^ k := by
  induction k with
  | zero => simp [dyadicSearch]
  | succ k ih =>
    rw [abs_lt] at ih ⊢
    simp only [dyadicSearch, pow_succ]
    split <;> omega

theorem dyadicQuery_coeff_le {p : ℕ} (a b : Fin p → ℤ) (k : ℕ) (n : ℤ)
    (hn : |n| ≤ 2 ^ k) (i : Fin p) :
    |dyadicQuery a b k n i| ≤ 2 ^ k * (|a i| + |b i|) := by
  calc
    _ ≤ |(2 : ℤ) ^ k * a i| + |n * b i| := abs_sub ..
    _ = 2 ^ k * |a i| + |n| * |b i| := by simp [abs_mul]
    _ ≤ 2 ^ k * |a i| + 2 ^ k * |b i| := by gcongr
    _ = _ := by ring

theorem dyadicSearch_query_coeff_bound {p : ℕ} (oracle : (Fin p → ℤ) → Bool)
    (a b : Fin p → ℤ) (k : ℕ) {query : Fin p → ℤ}
    (hm : query ∈ (dyadicSearch oracle a b k).queries) (i : Fin p) :
    |query i| ≤ 2 ^ k * (|a i| + |b i|) := by
  induction k with
  | zero => simp [dyadicSearch] at hm
  | succ k ih =>
    have hp : (2 : ℤ) ^ k ≤ 2 ^ (k+1) := by rw [pow_succ]; have := (show 0 ≤ (2 : ℤ)^k by positivity); omega
    have hmul := mul_le_mul_of_nonneg_right hp (add_nonneg (abs_nonneg (a i)) (abs_nonneg (b i)))
    rcases List.mem_cons.mp hm with h | h
    · subst query
      exact (dyadicQuery_coeff_le a b k _ (dyadicSearch_numerator_lt oracle a b k).le i).trans hmul
    · exact (ih h).trans hmul

private theorem dyadicSearch_scaled_error {p : ℕ} (oracle : (Fin p → ℤ) → Bool)
    (a b : Fin p → ℤ) (v : Fin p → ℝ) (hOracle : ∀ c, oracle c = true ↔ 0 ≤ formValue c v)
    (hab : |formValue a v| ≤ formValue b v) (k : ℕ) :
    |(2 : ℝ) ^ k * formValue a v - (dyadicSearch oracle a b k).numerator * formValue b v| ≤
      formValue b v := by
  induction k with
  | zero => simpa [dyadicSearch] using hab
  | succ k ih =>
    have hsign := hOracle (dyadicQuery a b k (dyadicSearch oracle a b k).numerator)
    rw [dyadicQuery_value] at hsign
    rw [abs_le] at ih ⊢
    simp only [dyadicSearch, pow_succ]
    split
    · rename_i h
      have h' := hsign.mp h
      push_cast
      constructor <;> linarith
    · rename_i h
      have h' := lt_of_not_ge (fun h' => h (hsign.mpr h'))
      push_cast
      constructor <;> linarith

/-- Approximate a normalized coordinate to `2⁻ᵏ` using only comparison of integer forms. -/
theorem dyadicSearch_ratio_error {p : ℕ} (oracle : (Fin p → ℤ) → Bool)
    (a b : Fin p → ℤ) (v : Fin p → ℝ) (hOracle : ∀ c, oracle c = true ↔ 0 ≤ formValue c v)
    (hb : 0 < formValue b v) (hab : |formValue a v| ≤ formValue b v) (k : ℕ) :
    |formValue a v / formValue b v - (dyadicSearch oracle a b k).numerator / (2 : ℝ) ^ k| ≤
      1 / (2 : ℝ) ^ k := by
  have hpow : 0 < (2 : ℝ) ^ k := by positivity
  have hs := dyadicSearch_scaled_error oracle a b v hOracle hab k
  rw [div_sub_div _ _ hb.ne' hpow.ne', abs_div, abs_of_pos (mul_pos hb hpow),
      div_le_div_iff₀ (mul_pos hb hpow) hpow]
  simpa [mul_comm] using mul_le_mul_of_nonneg_right hs hpow.le

end Lattice
end LinearProgramming
end Optimization
end OAI
