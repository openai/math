import OAI.Computability.BorderVNP.ModelSpecializationMap
import OAI.Computability.BorderVNP.ModelSubstitute
import OAI.Computability.BorderVNP.ModelHomogenize

/-!
# Specialization at the border

Lemma 2.1 and equation (12.1), in the commutative model. The exact homogeneous
component of each approximant is computed before substitution. The desired target
degree is then read directly from the resulting circuit output.
-/

namespace OAI
namespace Computability
namespace BorderVNP

open MvPolynomial VPVNP

variable {K F σ τ : Type*} [Field K] [Field F] [Finite σ] {d e s m : ℕ}

private theorem attained_of_circuitSize {k : ℕ} (e : ℕ) {p : MvPolynomial τ K}
    (h : circuitSize p ≤ k) : coeffVector e p ∈ circuitImage K τ e k := by
  obtain ⟨c, hc⟩ := circuitSize_spec p
  exact ⟨_, h, c, congrArg (coeffVector e) hc⟩

/-- Substituting the outputs of a single shared input program into the exact degree-`d`
component costs that program's size once, even at a point of the image closure. -/
theorem geometricApprox_aeval_shared (P : Program K τ m) (a : σ → Ref K τ m) (e : ℕ)
    {p : MvPolynomial σ K} (h : geometricApprox d s p) :
    geometricApprox e (m + 2 * (d + 1)^2 * s)
      (aeval (fun i => (⟨P, a i⟩ : Circuit K τ m).polynomial) (homogeneousComponent d p)) := by
  refine geometricApprox_componentMap h
    (aeval (fun i => (⟨P, a i⟩ : Circuit K τ m).polynomial)).toLinearMap ?_
  intro n hn c
  apply attained_of_circuitSize
  exact (circuitSize_aeval_shared P a _).trans (Nat.add_le_add_left
    ((circuitSize_homogeneousComponent_le d c.polynomial).trans (Nat.mul_le_mul_left _
      ((circuitSize_le_of_circuit c).trans hn))) m)

/-- A projection by variables and scalars adds no input-computation gates. It is applied
after extracting the degree-`d` component of the approximant. -/
theorem geometricApprox_projection (φ : Projection K σ τ) (e : ℕ) {p : MvPolynomial σ K}
    (h : geometricApprox d s p) :
    geometricApprox e (2 * (d + 1)^2 * s) (φ.hom (homogeneousComponent d p)) := by
  refine geometricApprox_componentMap h
    (aeval (fun i => (φ i).elim (X : τ → MvPolynomial τ K) C)).toLinearMap ?_
  intro n hn c
  apply attained_of_circuitSize
  exact (circuitSize_projection_le φ _).trans ((circuitSize_homogeneousComponent_le d c.polynomial).trans
    (Nat.mul_le_mul_left _ ((circuitSize_le_of_circuit c).trans hn)))

/-- Lemma 2.1 over the algebraic closure of the original scalar field. The shared
program for the substituted inputs can compute any polynomials, including affine forms. -/
theorem borderSize_aeval_shared_le (P : Program F τ m) (a : σ → Ref F τ m)
    {p : MvPolynomial σ F} (hp : p.IsHomogeneous d) (e : ℕ) :
    borderSize e (aeval (fun i => (⟨P, a i⟩ : Circuit F τ m).polynomial) p) ≤
      m + 2 * (d + 1)^2 * borderSize d p := by
  let hF := algebraMap F (AlgebraicClosure F)
  let P' := P.subst (S := AlgebraicClosure F) Sum.inl hF
  let a' := fun i => (a i).subst (S := AlgebraicClosure F) Sum.inl hF
  have base i : (⟨P', a' i⟩ : Circuit (AlgebraicClosure F) τ m).polynomial =
      map hF (⟨P, a i⟩ : Circuit F τ m).polynomial :=
    (⟨P, a i⟩ : Circuit F τ m).map_polynomial hF
  apply borderSize_le_iff.mpr
  change geometricApprox e _ (map hF (eval₂ C _ p))
  rw [map_eval₂]
  have h := geometricApprox_aeval_shared P' a' e (borderSize_spec d p)
  rw [homogeneousComponent_eq_self (hp.map hF)] at h
  change geometricApprox e _ (aeval (fun i => map hF (⟨P, a i⟩ : Circuit F τ m).polynomial) (map hF p))
  simpa only [base] using h

/-- Equation (12.1), with the explicit absolute constant 2. Source and target degrees may
differ since some variables may be set to scalars. -/
theorem borderSize_projection_le (φ : Projection F σ τ) {p : MvPolynomial σ F}
    (hp : p.IsHomogeneous d) (e : ℕ) :
    borderSize e (φ.hom p) ≤ 2 * (d + 1)^2 * borderSize d p := by
  let a : σ → Ref F τ 0 := fun i => (φ i).elim .var .const
  have inputs i : (⟨.nil, a i⟩ : Circuit F τ 0).polynomial =
      (φ i).elim X C := by
    cases h : φ i <;> simp [a, h, Circuit.polynomial, Circuit.eval, Ref.read]
  have bound := borderSize_aeval_shared_le .nil a hp e
  change borderSize e (aeval (fun i => (φ i).elim X C) p) ≤ _
  simpa only [inputs, Nat.zero_add] using bound

end BorderVNP
end Computability
end OAI
