import OAI.Computability.BorderVNP.Model

/-!
# Linear operations on degree components

A fixed linear operation on formal polynomials induces a polynomial map on the coefficient
space of forms of a given degree. This lets us pass from a construction on actual circuits
to a statement on their image closures, in the order required in §2.1.
-/

namespace OAI
namespace Computability
namespace BorderVNP

open MvPolynomial

variable {K σ τ : Type*} [Field K] [Finite σ]

/-- Expand the exact homogeneous component in the basis of degree-`d` monomials. -/
theorem homogeneousComponent_eq_sum_basis (d : ℕ) (p : MvPolynomial σ K) :
    let _ := Fintype.ofFinite (DegreeMonomial σ d)
    homogeneousComponent d p =
      ∑ i : DegreeMonomial σ d, coeffVector d p i • monomial i.val (1 : K) := by
  classical
  let _ := Fintype.ofFinite (DegreeMonomial σ d)
  ext m
  rw [coeff_homogeneousComponent, coeff_sum]
  by_cases hm : m.degree = d
  · simp only [hm, ite_true]
    symm
    trans (coeffVector d p (⟨m, hm⟩ : DegreeMonomial σ d) • monomial m (1 : K)).coeff m
    · apply Finset.sum_eq_single (⟨m, hm⟩ : DegreeMonomial σ d)
      · intro i _ h
        have hi : i.val ≠ m := fun e => h (Subtype.ext e)
        simp [smul_monomial, coeff_monomial, hi]
      · exact fun h => (h (@Finset.mem_univ (DegreeMonomial σ d) (Fintype.ofFinite _) ⟨m, hm⟩)).elim
    · simp [coeffVector, smul_monomial, coeff_monomial]
  · simp only [hm, ite_false]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hi : i.val ≠ m := fun e => hm (e ▸ i.property)
    simp [smul_monomial, coeff_monomial, hi]

/-- Polynomial giving a target coefficient after a fixed linear operation on homogeneous
degree-`d` inputs. -/
noncomputable def componentCoordinate (d e : ℕ) (f : MvPolynomial σ K →ₗ[K] MvPolynomial τ K)
    (j : DegreeMonomial τ e) : MvPolynomial (DegreeMonomial σ d) K := by
  classical
  let _ := Fintype.ofFinite (DegreeMonomial σ d)
  exact ∑ i : DegreeMonomial σ d, X i * C ((f (monomial i.val 1)).coeff j.val)

/-- Evaluating the coordinate polynomials applies the linear operation to the extracted form. -/
theorem eval_componentCoordinate (d e : ℕ) (f : MvPolynomial σ K →ₗ[K] MvPolynomial τ K)
    (p : MvPolynomial σ K) :
    (fun j => eval (coeffVector d p) (componentCoordinate d e f j)) =
      coeffVector e (f (homogeneousComponent d p)) := by
  classical
  let _ := Fintype.ofFinite (DegreeMonomial σ d)
  funext j
  rw [homogeneousComponent_eq_sum_basis]
  simp [coeffVector, componentCoordinate, map_sum]

/-- To transport an approximation, it suffices to implement the linear operation on actual
degree-`d` circuit outputs and realize their target coefficients with the new gate budget. -/
theorem geometricApprox_componentMap {d e s t : ℕ} {p : MvPolynomial σ K}
    (h : geometricApprox d s p) (f : MvPolynomial σ K →ₗ[K] MvPolynomial τ K)
    (hf : ∀ m ≤ s, ∀ c : VPVNP.Circuit K σ m,
      coeffVector e (f (homogeneousComponent d c.polynomial)) ∈ circuitImage K τ e t) :
    geometricApprox e t (f (homogeneousComponent d p)) := by
  unfold geometricApprox
  rw [← eval_componentCoordinate]
  refine imageClosure_mono ?_ (imageClosure_polynomial h (componentCoordinate d e f))
  rintro _ ⟨_, ⟨m, hm, c, rfl⟩, rfl⟩
  change (fun j => eval (coeffVector d c.polynomial) (componentCoordinate d e f j)) ∈ _
  rw [eval_componentCoordinate]
  exact hf m hm c

end BorderVNP
end Computability
end OAI
