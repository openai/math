import OAI.Computability.BorderVNP.GeneratorSliceComponents
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! # Finiteness of the nonsingular locus of a square fiber

The finite-difference matrix gives an explicit polynomial isolating each
simple zero. Its determinant specializes to the Jacobian there. Thus each
simple zero contributes a different minimal prime, even if the cleared
equations have positive-dimensional components elsewhere.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial
open scoped Matrix

private theorem finite_difference {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι F) (x : ι → F) :
    ∃ D : ι → MvPolynomial ι F, (∀ y, eval y p - eval x p =
        ∑ j, eval y (D j) * (y j - x j)) ∧ ∀ j, eval x (D j) = eval x (pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨0, by simp, by simp⟩
  | add p q hp hq =>
    obtain ⟨D, hD, hd⟩ := hp
    obtain ⟨B, hB, hb⟩ := hq
    refine ⟨D+B, fun y => ?_, fun j => by simp [hd, hb]⟩
    simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib, ← hD, ← hB]
    abel
  | mul_X p i hp =>
    obtain ⟨D, hD, hd⟩ := hp
    refine ⟨fun j => D j * X i + if j = i then C (eval x p) else 0, fun y => ?_, fun j => ?_⟩
    · have hterm (j : ι) :
          eval y (D j * X i + if j = i then C (eval x p) else 0) * (y j - x j) =
          (eval y (D j) * (y j - x j)) * y i +
            (if j = i then eval x p * (y j - x j) else 0) := by
        by_cases hj : j = i <;> simp [hj] <;> ring
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← hD]
      simp
      ring
    · by_cases hj : j = i
      · subst j
        simp [hd, add_comm, mul_comm]
      · simp [hj, hd, mul_comm]

/-- The finite-difference determinant gives a principal open containing exactly the
selected nonsingular root of a square system. -/
theorem nonsingular_root_isolated {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (g : ι → MvPolynomial ι F) (x : ι → F) (hx : ∀ i, eval x (g i) = 0)
    (hJ : (Matrix.of fun i j => eval x (pderiv j (g i))).det ≠ 0) :
    ∃ P : MvPolynomial ι F, eval x P ≠ 0 ∧
      ∀ y : ι → F, (∀ i, eval y (g i) = 0) → eval y P ≠ 0 → y = x := by
  choose D hD hd using fun i => finite_difference (g i) x
  let M := Matrix.of D
  refine ⟨M.det, ?_, fun y hy hP => ?_⟩
  · rwa [(eval x).map_det, show (eval x).mapMatrix M =
        Matrix.of (fun i j => eval x (pderiv j (g i))) by ext i j; exact hd i j]
  rw [(eval y).map_det] at hP
  have hv : (M.map (eval y)) *ᵥ (y - x) = 0 := by
    funext i
    change (∑ j, eval y (D i j) * (y j - x j)) = 0
    rw [← hD i y, hy, hx, sub_zero]
  exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hP hv)

/-- Over an algebraically closed field the simple zeros of a square system form a finite
set, regardless of the dimension of the locus where the Jacobian vanishes. -/
theorem finite_nonsingular_roots {F : Type*} [Field F] [IsAlgClosed F] {h : ℕ}
    (g : Fin h → MvPolynomial (Fin h) F) :
    {x : Fin h → F | (∀ i, eval x (g i) = 0) ∧
      (Matrix.of fun i j => eval x (pderiv j (g i))).det ≠ 0}.Finite := by
  classical
  let J := Ideal.span (Set.range g)
  have hzero (x : Fin h → F) : x ∈ zeroLocus F J ↔ ∀ i, eval x (g i) = 0 := by
    simp [J, zeroLocus_span, aeval_eq_eval]
  apply Set.Finite.of_injOn (f := fun x : Fin h → F => vanishingIdeal F {x})
    (t := J.minimalPrimes) ?_ ?_ (Ideal.finite_minimalPrimes_of_isNoetherianRing _ J)
  · intro x hx
    obtain ⟨P, hp, hi⟩ := nonsingular_root_isolated g x hx.1 hx.2
    exact Generator.point_minimalPrime_of_isolating_polynomial ((hzero _).2 hx.1) hp
      (fun y hy => hi y ((hzero _).1 hy))
  · intro x _ y _ hxy
    funext j
    have hx : X j - C (x j) ∈ vanishingIdeal F {x} := by
      rw [mem_vanishingIdeal_singleton_iff]; simp
    have hy : X j - C (x j) ∈ vanishingIdeal F {y} := by
      change vanishingIdeal F {x} = vanishingIdeal F {y} at hxy
      rwa [← hxy]
    simpa [mem_vanishingIdeal_singleton_iff, sub_eq_zero, eq_comm] using hy

end Branch

end BorderVNP
end Computability
end OAI
