import OAI.LinearAlgebra.SpectralBooks.BorderCircuit
import OAI.LinearAlgebra.SpectralBooks.FormalPadding
import OAI.LinearAlgebra.SpectralBooks.HomogeneousCircuit

/-! # Polynomial projections in the degree-component border model

Taking a degree component before substituting variables and constants induces
a linear map on coefficient vectors. Homogenizing each exact circuit first
makes this map compatible with the quadratic gate bound, which then passes to
the Zariski closure over the algebraic closure of the ground field.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic MvPolynomial

noncomputable section

variable {F σ τ : Type*} [Field F]

private theorem homogeneousComponent_expand (D : ℕ) [Fintype (DegreeMonomial σ D)]
    (f : MvPolynomial σ F) :
    homogeneousComponent D f = ∑ m : DegreeMonomial σ D, C (f.coeff m.val) * monomial m.val 1 := by
  classical
  ext1 v
  simp only [coeff_homogeneousComponent, coeff_sum, C_mul_monomial, mul_one, coeff_monomial]
  by_cases hv : v.degree = D
  · let m : DegreeMonomial σ D := ⟨v, hv⟩
    rw [ite_eq_left_iff.mpr (by simp [hv]), Finset.sum_eq_single m]
    · simp [m]
    · intro j _ hj
      simp [show j.val ≠ v from fun he => hj (Subtype.ext he)]
    · simp
  · simp only [hv, reduceIte]
    symm
    apply Finset.sum_eq_zero
    intro m _
    simp [show m.val ≠ v from fun he => hv (he ▸ m.property)]

private def projectionCoordinates (D d : ℕ) [Fintype (DegreeMonomial σ D)]
    (z : σ → MvPolynomial τ F) (t : DegreeMonomial τ d) : MvPolynomial (DegreeMonomial σ D) F :=
  ∑ m : DegreeMonomial σ D, X m * C ((aeval z (monomial m.val (1 : F))).coeff t.val)

private theorem eval_projectionCoordinates (D d : ℕ) [Fintype (DegreeMonomial σ D)]
    (z : σ → MvPolynomial τ F) (f : MvPolynomial σ F) (t : DegreeMonomial τ d) :
    aeval (degreeCoefficientVector D f) (projectionCoordinates D d z t) =
      degreeCoefficientVector d (aeval z (homogeneousComponent D f)) t := by
  rw [homogeneousComponent_expand]
  simp [projectionCoordinates, degreeCoefficientVector, coeff_C_mul, aeval_eq_bind₁]

private theorem closure_projection [Fintype σ] (D d s : ℕ) (p : σ → τ ⊕ F)
    (f : MvPolynomial σ F)
    (hf : degreeCoefficientVector D f ∈ zeroLocus F (vanishingIdeal F (circuitCoefficientVectors F σ D s))) :
    degreeCoefficientVector d (aeval (fun i => Sum.elim X C (p i)) (homogeneousComponent D f)) ∈
      zeroLocus F (vanishingIdeal F (circuitCoefficientVectors F τ d (2*(D+1)^2*s))) := by
  classical
  let : Fintype (DegreeMonomial σ D) := (Finsupp.finite_of_degree_eq (σ := σ) D).fintype
  let z (i : σ) : MvPolynomial τ F := Sum.elim X C (p i)
  let a := projectionCoordinates D d z
  have ha (g : MvPolynomial σ F) :
      (fun t => aeval (degreeCoefficientVector D g) (a t)) =
        degreeCoefficientVector d (aeval z (homogeneousComponent D g)) :=
    funext (eval_projectionCoordinates D d z g)
  intro b hb
  change aeval (degreeCoefficientVector d (aeval z (homogeneousComponent D f))) b = 0
  rw [← ha, ← aeval_bind₁]
  apply hf
  rintro _ ⟨r, q, o, hcost, rfl⟩
  change aeval _ (bind₁ a b) = 0
  rw [aeval_bind₁, ha]
  apply hb
  obtain ⟨r', q', out, hout, hbound⟩ := exists_homogeneousComponent_program D q
  let k : Fin (D+1) := ⟨D, by omega⟩
  refine ⟨r', q'.mapSource p, out o k, ?_, ?_⟩
  · simpa only [Program.cost_mapSource] using hbound.trans (Nat.mul_le_mul_left _ hcost)
  · rw [registerPolynomial_mapSource, hout]

/-- A projection of a degree-`D` homogeneous polynomial, with arbitrary
variables and field constants, costs at most `2*(D+1)^2` times its
degree-`D` border size. The projected degree `d` can be chosen arbitrarily. -/
theorem degreeBorderSize_projection_le [Fintype σ] (D d : ℕ) (p : σ → τ ⊕ F)
    (f : MvPolynomial σ F) (hf : f.IsHomogeneous D) :
    degreeBorderSize d (aeval (fun i => Sum.elim X C (p i)) f) ≤
      2*(D+1)^2*degreeBorderSize D f := by
  let K := AlgebraicClosure F
  let h : F →+* K := algebraMap F K
  let q (i : σ) : τ ⊕ K := (p i).map id h
  have hq (i : σ) :
      map h (Sum.elim X C (p i) : MvPolynomial τ F) = Sum.elim X C (q i) := by
    cases e : p i <;> simp [q, e]
  have hmap : homogeneousComponent D (map h f) = map h f := by
    ext1 m
    have hcoeff := congrArg (fun g : MvPolynomial σ F => h (g.coeff m)) (homogeneousComponent_eq_self hf)
    simpa only [coeff_homogeneousComponent, coeff_map, apply_ite h, map_zero] using hcoeff
  apply (degreeBorderSize_le_iff ..).mpr
  change degreeCoefficientVector d (map h (aeval _ f)) ∈ _
  rw [aeval_eq_bind₁, map_bind₁, funext hq, ← aeval_eq_bind₁, ← hmap]
  exact closure_projection D d _ q (map h f) ((degreeBorderSize_le_iff D _ f).mp le_rfl)

end

end SpectralBooks
end LinearAlgebra
end OAI
