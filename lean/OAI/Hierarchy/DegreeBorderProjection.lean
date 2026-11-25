import OAI.Hierarchy.DegreeBorder
import OAI.Computability.BorderVNP.TransferIntegerGraph

namespace OAI
/-! # Projecting a homogeneous target in the degree-component border model -/

namespace Hierarchy

open Computability.VPVNP Computability.BorderVNP MvPolynomial

noncomputable section

variable {F K σ τ : Type*} [Field F] [Field K]

private theorem component_expansion (d : ℕ) [Fintype (DegreeMonomial σ d)]
    (p : MvPolynomial σ K) :
    homogeneousComponent d p = ∑ m : DegreeMonomial σ d, C (p.coeff m.1) * monomial m.1 1 := by
  classical
  ext1 v
  simp only [coeff_homogeneousComponent, coeff_sum, C_mul_monomial, mul_one, coeff_monomial]
  by_cases h : v.degree = d
  · let t : DegreeMonomial σ d := ⟨v,h⟩
    rw [ite_eq_left h, Finset.sum_eq_single t]
    · simp [t]
    · intro m _ hm
      simp [show m.1 ≠ v from fun e => hm (Subtype.ext e)]
    · simp
  · rw [ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro m _
    simp [show m.val ≠ v from fun e => h (e ▸ m.property)]

/-- Coordinates of the linear map obtained by extracting the source component,
performing the substitution and reading the destination component. -/
private def projectionEquation (D d : ℕ) [Fintype (DegreeMonomial σ D)]
    (φ : Projection K σ τ) (t : DegreeMonomial τ d) : MvPolynomial (DegreeMonomial σ D) K :=
  ∑ m : DegreeMonomial σ D, X m * C ((φ.hom (monomial m.1 (1 : K))).coeff t.1)

private theorem projectionEquation_eval (D d : ℕ) [Fintype (DegreeMonomial σ D)]
    (φ : Projection K σ τ) (p : MvPolynomial σ K) (t : DegreeMonomial τ d) :
    eval (coeffVector D p) (projectionEquation D d φ t) =
      coeffVector d (φ.hom (homogeneousComponent D p)) t := by
  rw [component_expansion]
  simp [projectionEquation, coeffVector, coeff_C_mul, Projection.hom, map_sum]

/-- Any bounded exact simulation of the extracted component under projection
transfers the same cost bound to degree-component border approximation. -/
theorem degreeModelClosure_projection [Finite σ] (D d s t : ℕ)
    (model : ℕ → MvPolynomial σ K → Prop) (other : ℕ → MvPolynomial τ K → Prop)
    (φ : Projection K σ τ) (p : MvPolynomial σ K)
    (hs : coeffVector D p ∈ degreeModelClosure model D s)
    (simulation : ∀ g, model s g → other t (φ.hom (homogeneousComponent D g))) :
    coeffVector d (φ.hom (homogeneousComponent D p)) ∈ degreeModelClosure other d t := by
  classical
  let := Fintype.ofFinite (DegreeMonomial σ D)
  let coordinates := projectionEquation D d φ
  have transform (g : MvPolynomial σ K) :
      (fun i => eval (coeffVector D g) (coordinates i)) =
        coeffVector d (φ.hom (homogeneousComponent D g)) :=
    funext (projectionEquation_eval D d φ g)
  rw [← transform]
  apply imageClosure_mono _ (imageClosure_polynomial hs coordinates)
  rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  exact ⟨_, simulation g hg, (transform g).symm⟩

theorem DegreeBorderAtMost.projection [Finite σ] {D d s t : ℕ}
    {model : ℕ → MvPolynomial σ (AlgebraicClosure F) → Prop}
    {other : ℕ → MvPolynomial τ (AlgebraicClosure F) → Prop}
    (φ : Projection F σ τ) {p : MvPolynomial σ F} (homogeneous : p.IsHomogeneous D)
    (h : DegreeBorderAtMost model D s p)
    (simulation : ∀ g, model s g → other t
      ((castProjection (algebraMap F (AlgebraicClosure F)) φ).hom (homogeneousComponent D g))) :
    DegreeBorderAtMost other d t (φ.hom p) := by
  let α := algebraMap F (AlgebraicClosure F)
  have component : homogeneousComponent D (map α p) = map α p := by
    ext1 m
    have hc := congrArg (fun g : MvPolynomial σ F => α (g.coeff m))
      (homogeneousComponent_eq_self homogeneous)
    simpa only [coeff_homogeneousComponent, coeff_map, apply_ite α, map_zero] using hc
  change coeffVector d (map α (φ.hom p)) ∈ _
  rw [map_projection_hom, ← component]
  exact degreeModelClosure_projection D d s t model other _ _ h simulation

end
end Hierarchy

end OAI
