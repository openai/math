import OAI.LinearAlgebra.FiniteFourier.CircuitComposition
import OAI.LinearAlgebra.FiniteFourier.CircuitReindex
import OAI.LinearAlgebra.SpectralBooks.FormalCircuit
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # Pinned arithmetic circuits

After specializing at a fixed input, the differential of every scalar gate takes
at most one binary linear gate. All output differentials share the same
straight-line program. The formal polynomials can have integral coefficients
and the evaluation field can have arbitrary characteristic.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open MvPolynomial OAI.LinearAlgebra.SpectralBooks
open scoped BigOperators

variable {R K I O : Type*} [CommRing R] [Fintype I]

section CommRing

variable [CommRing K]

/-- The row of the Jacobian for a single output polynomial at a chosen input. -/
noncomputable def derivativeRow (φ : R →+* K) (u : I → K) (p : MvPolynomial I R) (i : I) : K :=
  eval₂Hom φ u (pderiv i p)

private noncomputable def differential (φ : R →+* K) (u : I → K) (p : MvPolynomial I R) (x : I → K) :
    K := ∑ i, derivativeRow φ u p i * x i

private theorem differential_mul (φ : R →+* K) (u : I → K) (p q : MvPolynomial I R) (x : I → K) :
    differential φ u (p*q) x = eval₂Hom φ u q * differential φ u p x +
      eval₂Hom φ u p * differential φ u q x := by
  simp only [differential, derivativeRow, pderiv_mul, map_add, map_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

private theorem simulateDifferential (φ : R →+* K) (u : I → K) {r : ℕ}
    (P : MatrixMultiplication.Arithmetic.Program R I r) :
    ∃ n ≤ P.cost, ∃ q : Program K I n,
      ∀ j, Available q (differential φ u (registerPolynomial P j)) := by
  classical
  induction P with
  | nil => exact ⟨0, le_rfl, .nil, fun i => i.elim0⟩
  | @step r p g ih =>
    obtain ⟨n, hn, q, hq⟩ := ih
    cases g with
    | constant c =>
      refine ⟨n, hn, q, Fin.cases ?_ hq⟩
      exact ⟨.zero, fun x => by simp [gatePolynomial, differential, derivativeRow, Readout.eval]⟩
    | input i =>
      refine ⟨n, hn, q, Fin.cases ?_ hq⟩
      refine ⟨.scaled 1 (.inl i), fun x => ?_⟩
      simp [gatePolynomial, differential, derivativeRow, Readout.eval, pderiv_X, Pi.single_apply,
        apply_ite, ite_mul]
    | add i j =>
      obtain ⟨m, hm, v, keep, out⟩ := available_combine q 1 1 (hq i) (hq j)
      refine ⟨m, hm.trans (Nat.add_le_add_right hn 1), v, Fin.cases ?_ (fun k => keep _ (hq k))⟩
      convert out using 1
      funext x
      simp [gatePolynomial, differential, derivativeRow, add_mul, Finset.sum_add_distrib]
    | sub i j =>
      obtain ⟨m, hm, v, keep, out⟩ := available_combine q 1 (-1) (hq i) (hq j)
      refine ⟨m, hm.trans (Nat.add_le_add_right hn 1), v, Fin.cases ?_ (fun k => keep _ (hq k))⟩
      convert out using 1
      funext x
      simp [gatePolynomial, differential, derivativeRow, add_mul, Finset.sum_add_distrib,
        sub_eq_add_neg]
    | mul i j =>
      obtain ⟨m, hm, v, keep, out⟩ := available_combine q
        (eval₂Hom φ u (registerPolynomial p j)) (eval₂Hom φ u (registerPolynomial p i))
        (hq i) (hq j)
      refine ⟨m, hm.trans (Nat.add_le_add_right hn 1), v, Fin.cases ?_ (fun k => keep _ (hq k))⟩
      convert out using 1
      funext x
      simp [gatePolynomial, differential_mul]

/-- A forward differential circuit works over any commutative coefficient
ring. Its linear coefficients are evaluated in that ring. -/
theorem exists_circuit_jacobian (φ : R →+* K) (u : I → K) {r : ℕ}
    (P : MatrixMultiplication.Arithmetic.Program R I r) (out : O → Fin r) :
    ∃ n ≤ P.cost, ∃ q : Circuit K I O n, ∀ x o,
      q.eval x o = ∑ i, derivativeRow φ u (registerPolynomial P (out o)) i * x i := by
  classical
  obtain ⟨n, hn, q, hv⟩ := simulateDifferential φ u P
  choose z hz using fun o => hv (out o)
  exact ⟨n, hn, ⟨q, z⟩, fun x o => hz o x⟩

end CommRing

/-- All rows of the formal Jacobian, after coefficient specialization, have a shared
binary linear circuit with at most the original number of arithmetic gates. -/
theorem realizableAtMost_jacobian [Field K] (φ : R →+* K) (u : I → K) {r : ℕ}
    (P : MatrixMultiplication.Arithmetic.Program R I r) (out : O → Fin r) :
    RealizableAtMost (Matrix.of (fun o i => derivativeRow φ u (registerPolynomial P (out o)) i)) P.cost := by
  classical
  obtain ⟨n, hn, q, hq⟩ := exists_circuit_jacobian φ u P out
  refine ⟨n, hn, q, ?_⟩
  ext o i
  simp [Circuit.matrix_apply, hq, Pi.single_apply, mul_ite]

end FiniteFourier
end LinearAlgebra
end OAI
