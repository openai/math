import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Log

/-!
# Streaming coefficient queries for matrix powers

A query for one coefficient of a polynomial matrix power in Appendix D.2
splits its exponent into two halves. The implementation scans intermediate
indices and degree splits with scalar accumulators.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery

open Polynomial

/-- Splitting a nontrivial exponent into its lower and upper halves decreases
the ceiling binary logarithm by at least one on both branches. -/
theorem powerQuery_halves {h : ℕ} (hh : 1 < h) :
    Nat.clog 2 (h / 2) < Nat.clog 2 h ∧ Nat.clog 2 (h - h / 2) < Nat.clog 2 h := by
  have upper : h - h / 2 = (h + 2 - 1) / 2 := by omega
  have order : h / 2 ≤ h - h / 2 := by omega
  have step : Nat.clog 2 h = Nat.clog 2 (h - h / 2) + 1 := by
    rw [upper]
    exact Nat.clog_of_one_lt (by decide) hh
  exact ⟨lt_of_le_of_lt (Nat.clog_mono_right 2 order) (by omega), by omega⟩

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]

/-- From an oracle for coefficients of individual entries, compute the
coefficient of degree `z` in entry `(i,j)` of the `h`-th power. -/
def powerEntryCoeff (entry : ι → ι → ℕ → R) (h : ℕ) (i j : ι) (z : ℕ) : R :=
  if h = 0 then
    if i = j ∧ z = 0 then 1 else 0
  else if h = 1 then
    entry i j z
  else
    ∑ k : ι, ∑ d ∈ Finset.antidiagonal z,
      powerEntryCoeff entry (h / 2) i k d.1 *
        powerEntryCoeff entry (h - h / 2) k j d.2
termination_by Nat.clog 2 h
decreasing_by
  · exact (powerQuery_halves (by omega)).1
  · exact (powerQuery_halves (by omega)).2

/-- The entry query returns exactly the specified coefficient of the matrix
power, using only the supplied entry oracle. -/
theorem powerEntryCoeff_correct (M : Matrix ι ι R[X]) (entry : ι → ι → ℕ → R)
    (hentry : ∀ i j z, entry i j z = (M i j).coeff z) (h : ℕ) (i j : ι) (z : ℕ) :
    powerEntryCoeff entry h i j z = ((M ^ h) i j).coeff z := by
  induction h using Nat.strong_induction_on generalizing i j z with
  | h h ih =>
    by_cases hz : h = 0
    · subst h
      by_cases hij : i = j <;> simp [powerEntryCoeff, hij, coeff_one]
    by_cases ho : h = 1
    · subst h
      simpa [powerEntryCoeff] using hentry i j z
    rw [powerEntryCoeff, ite_eq_right hz, ite_eq_right ho]
    have splitPow : M ^ h = M ^ (h / 2) * M ^ (h - h / 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [splitPow, Matrix.mul_apply, finsetSum_coeff]
    simp_rw [coeff_mul, ih (h / 2) (by omega), ih (h - h / 2) (by omega)]

/-- A sequential scan over all indices uses a scalar accumulator. -/
theorem foldl_add_eq_sum {A : Type*} [AddCommMonoid A]
    (n : ℕ) (f : Fin n → A) :
    Fin.foldl n (fun a i => a + f i) 0 = ∑ i, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
    simp only [ih]

/-- Sum over a consecutive block of indices with a tail-recursive scan. -/
def streamSum {A : Type*} [AddCommMonoid A] (n : ℕ) (f : Fin n → A) : A :=
  Fin.foldl n (fun acc i => acc + f i) 0

theorem streamSum_eq {A : Type*} [AddCommMonoid A] (n : ℕ) (f : Fin n → A) :
    streamSum n f = ∑ i, f i :=
  foldl_add_eq_sum n f

/-- Stream the ordered degree splits of `n` by keeping the first degree as
the loop index and computing the second by subtraction. -/
def streamAntiSum {A : Type*} [AddCommMonoid A] (n : ℕ) (f : ℕ → ℕ → A) : A :=
  streamSum (n + 1) fun i => f i.val (n - i.val)

theorem streamAntiSum_eq {A : Type*} [AddCommMonoid A] (n : ℕ) (f : ℕ → ℕ → A) :
    streamAntiSum n f = ∑ p ∈ Finset.antidiagonal n, f p.1 p.2 := by
  rw [streamAntiSum, streamSum_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ f]
  exact Fin.sum_univ_eq_sum_range (fun i => f i (n - i)) (n + 1)

/-- Streaming implementation for matrices indexed by consecutive integers.
The tail-recursive folds carry the two running sums for intermediate indices
and for degree splits. Neither loop stores a list of all its indices. -/
def streamedPowerEntryCoeff {n : ℕ} (entry : Fin n → Fin n → ℕ → R)
    (h : ℕ) (i j : Fin n) (z : ℕ) : R :=
  if h = 0 then
    if i = j ∧ z = 0 then 1 else 0
  else if h = 1 then
    entry i j z
  else
    Fin.foldl n (fun acc k => acc +
      Fin.foldl (z + 1) (fun acc' d => acc' +
        streamedPowerEntryCoeff entry (h / 2) i k d.val *
          streamedPowerEntryCoeff entry (h - h / 2) k j (z - d.val)) 0) 0
termination_by Nat.clog 2 h
decreasing_by
  · exact (powerQuery_halves (by omega)).1
  · exact (powerQuery_halves (by omega)).2

/-- The streaming loops evaluate the matrix-power coefficient recurrence. -/
theorem streamedPowerEntryCoeff_eq {n : ℕ} (entry : Fin n → Fin n → ℕ → R)
    (h : ℕ) (i j : Fin n) (z : ℕ) :
    streamedPowerEntryCoeff entry h i j z = powerEntryCoeff entry h i j z := by
  induction h using Nat.strong_induction_on generalizing i j z with
  | h h ih =>
    rw [streamedPowerEntryCoeff, powerEntryCoeff]
    split_ifs with hzero _ hone <;> try rfl
    simp_rw [foldl_add_eq_sum, ih (h / 2) (by omega), ih (h - h / 2) (by omega)]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    exact Fin.sum_univ_eq_sum_range (fun d => powerEntryCoeff entry (h / 2) i k d *
      powerEntryCoeff entry (h - h / 2) k j (z - d)) (z + 1)

end RankQuery

end VPVNP
end Computability
end OAI
