import Mathlib.Algebra.Module.PID
import Mathlib.LinearAlgebra.AnnihilatingPolynomial

/-! # Annihilating polynomials from dependent Krylov chains -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- One vector detects whether any polynomial in a finite-dimensional endomorphism vanishes. -/
theorem exists_vector_detecting_aeval (f : Module.End K V) :
    ∃ x : V, ∀ g : K[X], (aeval f g) x = 0 ↔ aeval f g = 0 := by
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator K[X] (Module.AEval' f)
  refine ⟨(Module.AEval'.of f).symm x, fun g ↦ ?_⟩
  change g ∈ LinearMap.ker (LinearMap.toSpanSingleton K[X] _ x) ↔ _
  rw [hx, Module.AEval.annihilator_eq_ker_aeval]
  rfl

/-- If every orbit segment of length `b + 1` is dependent, one polynomial of degree at most
`b` annihilates the endomorphism on the whole space. -/
theorem exists_aeval_zero_of_forall_krylov_dependent (f : Module.End K V) (b : ℕ)
    (h : ∀ x : V, ¬ LinearIndependent K (fun i : Fin (b + 1) ↦ (f ^ (i : ℕ)) x)) :
    ∃ g : K[X], g ≠ 0 ∧ g.natDegree ≤ b ∧ aeval f g = 0 := by
  classical
  obtain ⟨x, hx⟩ := exists_vector_detecting_aeval f
  obtain ⟨c, hc, j, hj⟩ := Fintype.not_linearIndependent_iff.mp (h x)
  let g : K[X] := ∑ i : Fin (b + 1), monomial (i : ℕ) (c i)
  refine ⟨g, ?_, ?_, (hx g).mp ?_⟩
  · intro hg
    have he := congrArg (fun p : K[X] ↦ p.coeff j) hg
    apply hj
    simpa [g, finsetSum_coeff, coeff_monomial, Fin.val_inj] using he
  · exact natDegree_sum_le_of_forall_le _ _ fun i _ ↦ (natDegree_monomial_le _).trans
      (Nat.le_of_lt_succ i.isLt)
  · simpa [g, aeval_monomial, Module.End.mul_apply, LinearMap.sum_apply] using hc

end FiniteFourier
end LinearAlgebra
end OAI
