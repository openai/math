import OAI.Computability.BorderVNP.DecisionDeformationCurve
import OAI.Computability.BorderVNP.DecisionDeformationIncidence

/-! # Moving the isolated zero into a dense open

In the coordinate ring of the variety times the parameter line, test the map
`(t, G₁+tℓ₁, …, G_d+tℓ_d)` against a general line `(t,tc₁,…,tc_d)`.
The fiber over a transcendental parameter is finite on all affine coordinates
and avoids the specified hypersurface. The special fiber still contains the
chosen isolated point, through which a horizontal curve passes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Decision

open Polynomial
variable {K E A : Type*} [Field K] [Infinite K] [Field E] [Algebra K E]
  [CommRing A] [IsDomain A] [Algebra E A] [Algebra.FiniteType E A]

/-- Transcendence degree of an affine domain is the height of a closed
point. This identifies the algebraic dependence count in the incidence
argument with the number of equations in the local cut. -/
theorem trdeg_at_closed_point {d : ℕ} (m : Ideal A) [m.IsMaximal] (height : m.height = d) :
    Algebra.trdeg E A = d := by
  obtain ⟨n, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg E A
  obtain ⟨he, hdim⟩ := Branch.dimension_of_normalization m n g hinj hint
  have nd : n = d := by exact_mod_cast (hdim.symm.trans (he.symm.trans (congrArg _ height)))
  let R := MvPolynomial (Fin n) E
  let : Algebra R A := g.toRingHom.toAlgebra
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : IsScalarTower E R A := IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  have : Algebra.IsIntegral R A := ⟨hint⟩
  have hb := (IsTranscendenceBasis.mvPolynomial (Fin n) E).algebraMap_comp (A := A)
  simpa [nd] using hb.lift_cardinalMk_eq_trdeg.symm

/-- The tuple of deformed equations, with constant perturbations chosen over
the ground field. -/
noncomputable def movingEquations {d : ℕ} (G ℓ : Fin d → A) (c : Fin d → K) :
    Fin d → Polynomial A :=
  fun i => perturbEquation (G i) (ℓ i - algebraMap E A (algebraMap K E (c i)))

/-- Values of the affine coordinates on the geometric fiber at `t`. -/
def movingFiber {d n : ℕ} {L : Type*} [Field L] [Algebra E L] (t : L)
    (coords : Fin n → A) (Q : Fin d → Polynomial A) : Set (Fin n → L) :=
  Set.range fun h : {h : Polynomial A →ₐ[E] L // h X = t ∧ ∀ i, h (Q i) = 0} =>
    fun j => h.val (C (coords j))

/-- Ground-field perturbations give finite generic fibers entirely in the
chosen dense open and a horizontal irreducible curve through the chosen
special zero. The open is specified by any nonzero polynomial function
on the total space, so it may include a Jacobian condition. -/
theorem move_isolated_zero (K : Type*) [Field K] [Infinite K] [Algebra K E] {d n : ℕ}
    (m : Ideal A) [m.IsMaximal] (height : m.height = d) (G ℓ : Fin d → A)
    (isolated : m ∈ (Ideal.span (Set.range G)).minimalPrimes)
    (coords : Fin n → A) (avoid : Polynomial A) (hn : avoid ≠ 0) :
    ∃ c : Fin d → K, let Q := movingEquations (E := E) G ℓ c
      (∃ P ∈ (Ideal.span (Set.range Q)).minimalPrimes, P < m.comap constantCoeff ∧
        ringKrullDim (Polynomial A ⧸ P) = 1 ∧
        Function.Injective (Polynomial.aeval (R := E) (Ideal.Quotient.mk P X))) ∧
      ∀ (L : Type*) [Field L] [Algebra E L] (t : L), Transcendental E t →
        (movingFiber (E := E) t coords Q).Finite ∧
        ∀ h : Polynomial A →ₐ[E] L, h X = t → (∀ i, h (Q i) = 0) → h avoid ≠ 0 := by
  let outs := Fin.cons (α := fun _ => Polynomial A) X (fun i => perturbEquation (G i) (ℓ i))
  have dim : Algebra.trdeg E (Polynomial A) = ↑(d+1) := by
    rw [← trdeg_add_eq E A, trdeg_at_closed_point (E := E) m height, Polynomial.trdeg_of_isDomain,
      Nat.cast_succ]
  obtain ⟨test, htest, fiber⟩ := generic_finite_fiber_test (E := E) outs dim.le
    (fun j => C (coords j)) avoid hn
  obtain ⟨c, line⟩ := generic_line_avoids K htest
  let Q := movingEquations (E := E) G ℓ c
  refine ⟨c, deformation_curve (E := E) G (fun i => ℓ i - algebraMap E A (algebraMap K E (c i)))
    m height isolated, ?_⟩
  intro L _ _ t ht
  let b := Fin.cons (α := fun _ => L) t (fun i => t * algebraMap E L (algebraMap K E (c i)))
  obtain ⟨fin, good⟩ := fiber L b (line L t ht)
  have values (h : Polynomial A →ₐ[E] L) (hX : h X = t) (hQ : ∀ i, h (Q i) = 0) :
      ∀ i, h (outs i) = b i := by
    intro i
    refine Fin.cases hX (fun j => ?_) i
    have hs := hQ j
    change h (C (G j) + X * C (ℓ j - algebraMap E A (algebraMap K E (c j)))) = 0 at hs
    rw [map_add, map_mul, map_sub, map_sub, hX, mul_sub, ← add_sub_assoc, sub_eq_zero] at hs
    have hc : h (C (algebraMap E A (algebraMap K E (c j)))) = algebraMap E L (algebraMap K E (c j)) :=
      h.commutes _
    simpa only [outs, b, Fin.cons_succ, perturbEquation, map_add, map_mul, hX, hc] using hs
  refine ⟨fin.subset ?_, fun h hX hQ => good h (values h hX hQ)⟩
  rintro _ ⟨⟨h, hX, hQ⟩, rfl⟩
  exact ⟨⟨h, values h hX hQ⟩, rfl⟩

end Decision

end BorderVNP
end Computability
end OAI
