import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite orbit weights for the projective fixed-point argument

For a positive sequence with exponential upper bounds, choose its critical
geometric growth rate. Finite geometric weighted sums then have arbitrarily
large mass and arbitrarily small final-term fraction at rates approaching the
critical rate from below. This is the scalar ingredient of the compact convex
projective fixed-point proof; it uses no general fixed-point theorem.

The sums include indices `0, ..., n`. The terminal term is indexed by `n + 1`.
-/

noncomputable section

namespace OAI.LinearAlgebra.TensorSpectrum.MultiplicativeGrowth

open Set

/-- The normalization of a finite geometrically weighted orbit. -/
def weightedSum (a : ℕ → ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), a k / s ^ k

theorem weightedSum_zero (a : ℕ → ℝ) (s : ℝ) :
    weightedSum a s 0 = a 0 := by
  simp [weightedSum]

theorem weightedSum_succ (a : ℕ → ℝ) (s : ℝ) (n : ℕ) :
    weightedSum a s (n + 1) = weightedSum a s n + a (n + 1) / s ^ (n + 1) := by
  simp only [weightedSum, Finset.sum_range_succ]

theorem weightedSum_mono (a : ℕ → ℝ) (s : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hs : 0 < s) : Monotone (weightedSum a s) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [weightedSum_succ]
  exact le_add_of_nonneg_right (div_nonneg (ha _) (pow_nonneg hs.le _))

theorem weightedSum_term_le (a : ℕ → ℝ) (s : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hs : 0 < s) (n : ℕ) :
    a n / s ^ n ≤ weightedSum a s n := by
  apply Finset.single_le_sum (fun k _ => div_nonneg (ha k) (pow_nonneg hs.le k))
  exact Finset.mem_range.mpr (Nat.lt_succ_self n)

theorem one_le_weightedSum (a : ℕ → ℝ) (s : ℝ)
    (ha : ∀ n, 1 ≤ a n) (hs : 0 < s) (n : ℕ) :
    1 ≤ weightedSum a s n := by
  have hm := weightedSum_mono a s (fun k => (ha k).trans' zero_le_one) hs
  calc
    1 ≤ a 0 := ha 0
    _ = weightedSum a s 0 := (weightedSum_zero a s).symm
    _ ≤ weightedSum a s n := hm (Nat.zero_le n)

/-- Bernoulli's elementary inequality is enough for the only unboundedness
argument below. -/
private theorem exists_pow_gt (q : ℝ) (hq : 1 < q) (C : ℝ) :
    ∃ n : ℕ, C < q ^ n := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hbern : ∀ n : ℕ, 1 + (n : ℝ) * (q - 1) ≤ q ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        have hextra : 0 ≤ (n : ℝ) * (q - 1) ^ 2 := mul_nonneg hn (sq_nonneg _)
        calc
          1 + ((n + 1 : ℕ) : ℝ) * (q - 1) ≤
              (1 + (n : ℝ) * (q - 1)) * q := by
            push_cast
            nlinarith
          _ ≤ q ^ n * q := mul_le_mul_of_nonneg_right ih hq0.le
          _ = q ^ (n + 1) := (pow_succ q n).symm
  obtain ⟨n, hn⟩ := exists_nat_gt ((C - 1) / (q - 1))
  have hden : 0 < q - 1 := by linarith
  have hlarge := (div_lt_iff₀ hden).mp hn
  exact ⟨n, (by linarith : C < 1 + (n : ℝ) * (q - 1)).trans_le (hbern n)⟩

/-- A positive multiple of a strictly faster geometric sequence cannot be
bounded above by any fixed multiple of a slower one. -/
private theorem not_geometric_domination (u v A B : ℝ)
    (hv : 0 < v) (hvu : v < u) (hA : 0 < A) :
    ¬ (∀ n : ℕ, A * u ^ n ≤ B * v ^ n) := by
  intro h
  have hratio : 1 < u / v := (lt_div_iff₀ hv).mpr (by simpa using hvu)
  obtain ⟨n, hn⟩ := exists_pow_gt (u / v) hratio (B / A)
  rw [div_pow] at hn
  have hcross := (div_lt_div_iff₀ hA (pow_pos hv n)).mp hn
  have hbad := h n
  nlinarith

/-- Rates that give a uniform geometric upper bound for the scalar orbit. -/
private def geometricRates (a : ℕ → ℝ) : Set ℝ :=
  {t | 0 < t ∧ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, a n ≤ C * t ^ n}

private theorem geometricRates_upward (a : ℕ → ℝ) {t u : ℝ}
    (ht : t ∈ geometricRates a) (htu : t ≤ u) : u ∈ geometricRates a := by
  obtain ⟨ht0, C, hC, hbound⟩ := ht
  refine ⟨ht0.trans_le htu, C, hC, ?_⟩
  intro n
  exact (hbound n).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0.le htu n) hC.le)

private theorem geometricRates_one_le (a : ℕ → ℝ)
    (ha : ∀ n, 1 ≤ a n) {t : ℝ} (ht : t ∈ geometricRates a) : 1 ≤ t := by
  by_contra hnot
  have ht1 : t < 1 := lt_of_not_ge hnot
  obtain ⟨ht0, C, hC, hbound⟩ := ht
  apply not_geometric_domination 1 t 1 C ht0 ht1 zero_lt_one
  intro n
  simpa only [one_pow, one_mul] using (ha n).trans (hbound n)

private theorem above_inf_mem_geometricRates (a : ℕ → ℝ)
    (hne : (geometricRates a).Nonempty) {t : ℝ}
    (ht : sInf (geometricRates a) < t) : t ∈ geometricRates a := by
  by_contra hnot
  have hlow : t ≤ sInf (geometricRates a) := by
    apply le_csInf hne
    intro q hq
    by_contra hqt
    have hqt' : q < t := lt_of_not_ge hqt
    exact hnot (geometricRates_upward a hq hqt'.le)
  exact (not_le_of_gt ht) hlow

/-- Below the critical rate, the normalizing masses are unbounded. -/
private theorem weightedSum_unbounded (a : ℕ → ℝ)
    (ha : ∀ n, 1 ≤ a n) (hbelow : BddBelow (geometricRates a))
    {s : ℝ} (hs : 0 < s) (hsr : s < sInf (geometricRates a)) (L : ℝ) :
    ∃ n : ℕ, L < weightedSum a s n := by
  by_contra hnot
  have hbound : ∀ n : ℕ, weightedSum a s n ≤ L := by
    intro n
    exact le_of_not_gt (fun hn => hnot ⟨n, hn⟩)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one
    ((one_le_weightedSum a s ha hs 0).trans (hbound 0))
  have hrate : s ∈ geometricRates a := by
    refine ⟨hs, L, hL, ?_⟩
    intro n
    apply (div_le_iff₀ (pow_pos hs n)).mp
    exact (weightedSum_term_le a s (fun k => (ha k).trans' zero_le_one) hs n).trans
      (hbound n)
  exact (not_le_of_gt hsr) (csInf_le hbelow hrate)

/-- Fix any rate below the critical rate whose relative distance is small.
There are arbitrarily large normalizing masses with a small terminal fraction.
The proof is a contradiction between two distinct geometric growth rates. -/
private theorem near_rate_weights (a : ℕ → ℝ)
    (ha : ∀ n, 1 ≤ a n) (hne : (geometricRates a).Nonempty)
    (hbelow : BddBelow (geometricRates a))
    {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε)
    (hsr : s < sInf (geometricRates a))
    (hgap : sInf (geometricRates a) < s * (1 + ε)) (L : ℝ) :
    ∃ n : ℕ, L < weightedSum a s n ∧
      a (n + 1) / s ^ (n + 1) < ε * weightedSum a s n := by
  by_contra hnot
  let r : ℝ := sInf (geometricRates a)
  let u : ℝ := s * (1 + ε)
  let t : ℝ := (r + u) / 2
  have hrt : r < t := by dsimp [r, t, u]; linarith
  have htu : t < u := by dsimp [r, t, u]; linarith
  obtain ⟨ht0, C, hC, hCbound⟩ := above_inf_mem_geometricRates a hne hrt
  obtain ⟨N, hN⟩ := weightedSum_unbounded a ha hbelow hs hsr L
  have hmono := weightedSum_mono a s (fun k => (ha k).trans' zero_le_one) hs
  have hmass : 0 < weightedSum a s N :=
    zero_lt_one.trans_le (one_le_weightedSum a s ha hs N)
  have hterminal : ∀ k : ℕ,
      ε * weightedSum a s (N + k) ≤ a (N + k + 1) / s ^ (N + k + 1) := by
    intro k
    have hlarge : L < weightedSum a s (N + k) :=
      hN.trans_le (hmono (Nat.le_add_right N k))
    exact le_of_not_gt (fun hsmall => hnot ⟨N + k, hlarge, hsmall⟩)
  have hstep : ∀ k : ℕ,
      (1 + ε) * weightedSum a s (N + k) ≤ weightedSum a s (N + (k + 1)) := by
    intro k
    rw [show N + (k + 1) = (N + k) + 1 by omega, weightedSum_succ]
    have hterm := hterminal k
    nlinarith
  have hgrowth : ∀ k : ℕ,
      weightedSum a s N * (1 + ε) ^ k ≤ weightedSum a s (N + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          weightedSum a s N * (1 + ε) ^ (k + 1) =
              (1 + ε) * (weightedSum a s N * (1 + ε) ^ k) := by
            rw [pow_succ]
            ring
          _ ≤ (1 + ε) * weightedSum a s (N + k) :=
            mul_le_mul_of_nonneg_left ih (by linarith)
          _ ≤ weightedSum a s (N + (k + 1)) := hstep k
  let A : ℝ := ε * weightedSum a s N * s ^ (N + 1)
  have hA : 0 < A := by dsimp [A]; positivity
  apply not_geometric_domination u t A (C * t ^ (N + 1)) ht0 htu hA
  intro k
  calc
    A * u ^ k = (ε * (weightedSum a s N * (1 + ε) ^ k)) *
        s ^ (N + k + 1) := by
      dsimp [A, u]
      rw [mul_pow, show N + k + 1 = (N + 1) + k by omega, pow_add]
      ring
    _ ≤ (ε * weightedSum a s (N + k)) * s ^ (N + k + 1) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hgrowth k) hε.le) (pow_nonneg hs.le _)
    _ ≤ a (N + k + 1) := (le_div_iff₀ (pow_pos hs _)).mp (hterminal k)
    _ ≤ C * t ^ (N + k + 1) := hCbound _
    _ = (C * t ^ (N + 1)) * t ^ k := by
      rw [show N + k + 1 = (N + 1) + k by omega, pow_add]
      ring

/-- The scalar approximate-eigenvector selection used in Appendix A.2.
The rate `r` is fixed before the error tolerance and required mass are chosen. -/
theorem exists_approximate_weights (a : ℕ → ℝ) (M : ℝ)
    (ha : ∀ n, 1 ≤ a n) (hM : 1 ≤ M) (haM : ∀ n, a n ≤ M ^ n) :
    ∃ r : ℝ, 1 ≤ r ∧ r ≤ M ∧
      ∀ ε : ℝ, 0 < ε → ∀ L : ℝ,
        ∃ s : ℝ, ∃ n : ℕ, 0 < s ∧ s < r ∧ r - s < ε ∧
          L < weightedSum a s n ∧
          a (n + 1) / s ^ (n + 1) < ε * weightedSum a s n := by
  have hMmem : M ∈ geometricRates a := by
    refine ⟨zero_lt_one.trans_le hM, 1, zero_lt_one, ?_⟩
    intro n
    simpa only [one_mul] using haM n
  have hne : (geometricRates a).Nonempty := ⟨M, hMmem⟩
  have hbelow : BddBelow (geometricRates a) :=
    ⟨1, fun _ ht => geometricRates_one_le a ha ht⟩
  let r : ℝ := sInf (geometricRates a)
  have hr1 : 1 ≤ r := le_csInf hne (fun _ ht => geometricRates_one_le a ha ht)
  have hrM : r ≤ M := csInf_le hbelow hMmem
  have hr0 : 0 < r := zero_lt_one.trans_le hr1
  refine ⟨r, hr1, hrM, ?_⟩
  intro ε hε L
  let e : ℝ := min (ε / (2 * r)) (ε / 2)
  have he0 : 0 < e := by dsimp [e]; positivity
  have heε : e < ε := (min_le_right _ _).trans_lt (by linarith)
  have hre : r * e ≤ ε / 2 := by
    have he := (le_div_iff₀ (show 0 < 2 * r by positivity)).mp
      (show e ≤ ε / (2 * r) from min_le_left _ _)
    nlinarith
  let s : ℝ := r / (1 + e)
  have hs : 0 < s := by dsimp [s]; positivity
  have hseq : s * (1 + e) = r := by
    dsimp [s]
    exact div_mul_cancel₀ r (by positivity)
  have hsr : s < r := by nlinarith
  have hclose : r - s < ε := by
    have hse := mul_le_mul_of_nonneg_right hsr.le he0.le
    nlinarith
  have hgap : r < s * (1 + ε) := by nlinarith
  obtain ⟨n, hlarge, hsmall⟩ := near_rate_weights a ha hne hbelow hs hε hsr hgap L
  exact ⟨s, n, hs, hsr, hclose, hlarge, hsmall⟩

end OAI.LinearAlgebra.TensorSpectrum.MultiplicativeGrowth
