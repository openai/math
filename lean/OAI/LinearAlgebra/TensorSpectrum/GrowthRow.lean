import OAI.LinearAlgebra.TensorSpectrum.Growth
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Finite row bounds

For a concave positive row, one application of tripling bounds the row value
by a shifted index times the current increment.  Finite secant inequalities
then give the same bound for every increment.  Taking the infimum supplies
the slope required by the diagonal argument, without an asymptotic limit.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

def rowDifference (x : ℕ → ℝ) (n : ℕ) : ℝ := x (n + 1) - x n

theorem row_secant_bounds
    (x : ℕ → ℝ) (hdec : Antitone (rowDifference x)) (n k : ℕ) :
    x (n + k) ≤ x n + (k : ℝ) * rowDifference x n ∧
      x n + (k : ℝ) * rowDifference x (n + k) ≤ x (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hdn := hdec (show n ≤ n + k by omega)
      have hdk := hdec (show n + k ≤ n + (k + 1) by omega)
      have hscaled := mul_le_mul_of_nonneg_left hdk (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      have hdelta : x (n + (k + 1)) = x (n + k) + rowDifference x (n + k) := by
        dsimp [rowDifference]
        simp only [Nat.add_assoc]
        ring
      constructor
      · push_cast
        linarith [ih.1]
      · push_cast
        linarith [ih.2]

theorem row_local_bound
    (x : ℕ → ℝ) (a : ℕ)
    (hdec : Antitone (rowDifference x))
    (htrip : ∀ n : ℕ, 3 * x n ≤ x (3 * n + a + 1))
    (n : ℕ) :
    x n ≤ ((n : ℝ) + ((a : ℝ) + 1) / 2) * rowDifference x n := by
  have hsec := (row_secant_bounds x hdec n (2 * n + a + 1)).1
  have hindex : n + (2 * n + a + 1) = 3 * n + a + 1 := by omega
  rw [hindex] at hsec
  push_cast at hsec
  have ht := htrip n
  nlinarith

theorem row_bound_by_every_increment
    (x : ℕ → ℝ) (a : ℕ)
    (hdec : Antitone (rowDifference x))
    (htrip : ∀ n : ℕ, 3 * x n ≤ x (3 * n + a + 1))
    (n m : ℕ) :
    x n ≤ ((n : ℝ) + ((a : ℝ) + 1) / 2) * rowDifference x m := by
  rcases le_total n m with hnm | hmn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hlo := (row_secant_bounds x hdec n k).2
    have hup := row_local_bound x a hdec htrip (n + k)
    push_cast at hup
    linarith
  · have hd := hdec hmn
    have hc : 0 ≤ (n : ℝ) + ((a : ℝ) + 1) / 2 := by positivity
    exact (row_local_bound x a hdec htrip n).trans
      (mul_le_mul_of_nonneg_left hd hc)

noncomputable def rowSlope (x : ℕ → ℝ) : ℝ := sInf (Set.range (rowDifference x))

theorem row_slope_properties
    (x : ℕ → ℝ) (a : ℕ)
    (hpos : ∀ n : ℕ, 0 < x n)
    (hdec : Antitone (rowDifference x))
    (htrip : ∀ n : ℕ, 3 * x n ≤ x (3 * n + a + 1)) :
    0 ≤ rowSlope x ∧
      (∀ n : ℕ, rowSlope x ≤ rowDifference x n) ∧
      (∀ n : ℕ, x n ≤ ((n : ℝ) + ((a : ℝ) + 1) / 2) * rowSlope x) := by
  have hdnonneg : ∀ n : ℕ, 0 ≤ rowDifference x n := by
    intro n
    have hlocal := row_local_bound x a hdec htrip n
    have hc : 0 ≤ (n : ℝ) + ((a : ℝ) + 1) / 2 := by positivity
    by_contra! hneg
    have hm := mul_nonpos_of_nonneg_of_nonpos hc hneg.le
    linarith [hpos n]
  have hne : (Set.range (rowDifference x)).Nonempty := ⟨rowDifference x 0, 0, rfl⟩
  have hbounded : BddBelow (Set.range (rowDifference x)) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact hdnonneg n
  refine ⟨?_, ?_, ?_⟩
  · apply le_csInf hne
    rintro y ⟨n, rfl⟩
    exact hdnonneg n
  · intro n
    exact csInf_le hbounded ⟨n, rfl⟩
  · intro n
    have hc : 0 < (n : ℝ) + ((a : ℝ) + 1) / 2 := by positivity
    have hratio : x n / ((n : ℝ) + ((a : ℝ) + 1) / 2) ≤ rowSlope x := by
      apply le_csInf hne
      rintro y ⟨m, rfl⟩
      apply (div_le_iff₀ hc).mpr
      simpa [mul_comm] using row_bound_by_every_increment x a hdec htrip n m
    have hout := (div_le_iff₀ hc).mp hratio
    simpa [mul_comm] using hout

end OAI.LinearAlgebra.TensorSpectrum
