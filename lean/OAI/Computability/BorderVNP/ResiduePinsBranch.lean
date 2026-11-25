import OAI.Computability.BorderVNP.ResiduePinsFinite
import OAI.Computability.BorderVNP.ResidueSeparableParameter
import OAI.Computability.BorderVNP.ResidueApproximationMixed

/-! # Residue pins on the nonsingular parameter branch

The complete-intersection Cartier calculation and the trace-one approximation now
supply the analytic inputs to Lemma 10.1 on the actual completed discrete valuation ring.
The size of the Frobenius power is controlled by the pole budget of the finite tests.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResiduePins

open Residue ResidueBox Residue.JetRing Module Matrix IsLocalRing
open scoped Matrix BigOperators Classical

variable {σ β O E K : Type*} [Fintype σ] [DecidableEq σ] [Fintype β]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field E] [Fintype E] [Field K] [Algebra O K] [IsFractionRing O K] [Algebra E K]
  (p : ℕ) [Fact p.Prime] [CharP O p] [CharP (ResidueField O) p] [Finite (ResidueField O)]
  [CharP E p] [Algebra (ZMod p) E]

/-- The residue field of the completed branch carries the prime-field scalar action. -/
noncomputable local instance branchPrimeAlgebra : Algebra (ZMod p) (ResidueField O) :=
  ZMod.algebra _ _

/-- Lemma 10.1's nonzero pin and matrix action on the branch of §9. The branch generates
the function field, the parameter has positive order, the chart equations vanish, and the
Jacobian is nonsingular. The uniformizer proves that the parameter differential is nonzero. A single choice of power works for all
degree-bounded regular input polynomials with prime-field special value. -/
theorem branch_residue_pins (π : O) (hπ : Irreducible π) (x : σ → K) (t : Kˣ)
    (hgen : IntermediateField.adjoin E (insert (t : K) (Set.range x)) = ⊤)
    (B : Basis β (ZMod p) E) (L D : ℕ) (g : σ → MvPolynomial (Option σ) E) :
    let ρ := branchLaurentExpansion p π hπ K
    let φ := ρ.comp (algebraMap E K)
    let v := ρ ∘ x
    let τ := Units.map ρ.toMonoidHom t
    let y := fun i : Option σ => i.elim (τ : LaurentSeries (ResidueField O)) v
    let J := (chartJacobian φ y g).det
    let dt := LaurentSeries.derivative (ResidueField O) (τ : LaurentSeries (ResidueField O))
    let η₀ := dt / J
    let H := radius L (∑ j, (g j).totalDegree)
    let Ω := pin B H (testFunctional p φ v τ η₀)
    0 < (ρ (t : K)).order →
    (∀ i, MvPolynomial.eval₂Hom φ y (g i) = 0) →
    J ≠ 0 →
    (∀ i : Index β σ H, -(D : ℤ) ≤ (evaluate φ v τ (test B i) * η₀).order) →
    ∃ u > 0, D < p ^ u ∧ p ^ u ≤ Fintype.card E * max D 1 ∧ (∀ a : E, a ^ (p^u) = a) ∧ (∃ i, Ω i ≠ 0) ∧
      ∀ A : MvPolynomial σ E, A.totalDegree ≤ L → ∀ z : ZMod p,
        0 ≤ (MvPolynomial.eval₂ φ v A).order →
        (MvPolynomial.eval₂ φ v A).coeff 0 = algebraMap (ZMod p) (ResidueField O) z →
        (∑ μ ∈ A.support, weights B H (p ^ u) (pow_pos (Fact.out : p.Prime).pos u) g
          (RingHom.id E) (mixedIndex (polynomialIndex μ)) (A.coeff μ)) *ᵥ Ω = z • Ω := by
  intro ρ φ v τ y J dt η₀ H Ω ht hg hJ hpole
  have hparam : parameter (ResidueField O) ∈ Set.range ρ :=
    ⟨algebraMap O K π, branchLaurentExpansion_uniformizer p π hπ K⟩
  have hdt : dt ≠ 0 := branch_parameter_derivative_ne_zero p ρ x (t : K) hgen hparam g hg hJ
  apply residue_pins_of_branch p φ v τ η₀ B L D g _ _ hpole
  · intro u _
    exact pin_compatibility_iterate p g φ v τ η₀ (branch_formula_prime p g φ v τ hg hJ hdt) u
  · exact exists_trace_one_mixed p π hπ x t hgen ht η₀ (div_ne_zero hdt hJ)

end ResiduePins

end BorderVNP
end Computability
end OAI
