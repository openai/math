import OAI.Computability.BorderVNP.CrossingSplit
import OAI.Computability.BorderVNP.CrossingSplitRate
import OAI.Computability.BorderVNP.CrossingSplitSpecialization
import OAI.Computability.BorderVNP.ModelSpecialization

/-!
# Equation (4.3) for the signed source polynomial

The degree-`n` coefficient vector is approximated over the specified ambient field.
The substitution is applied to the exact degree-`n` component. The selected degree-`ℓ`
coefficients then have a balanced factorization in closure with a common rank bound.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open MvPolynomial VPVNP

variable {K I J : Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype J] {n s : ℕ}

/-- The balanced split of a projected side of the signed polynomial, with explicit
gate and rank overhead. The target is the closure of the sums, prior to any choice
of approximating tables at a boundary point. -/
theorem Pstar_projection_balancedCutSums (A : (I → J) → K)
    (φ : Projection K (Fin n × Bool) (I × J))
    (hφ : φ.hom (map (Int.castRingHom K) (Pstar n)) = sidePolynomial A)
    (hI : 3 ≤ Fintype.card I)
    (approx : geometricApprox n s (map (Int.castRingHom K) (Pstar n))) :
    A ∈ imageClosure (balancedCutSums I J K (splitWidth n (Fintype.card I) (Fintype.card J) s)) := by
  have hh := geometricApprox_projection φ (Fintype.card I) approx
  rw [homogeneousComponent_eq_self ((Pstar_isHomogeneous n).map (Int.castRingHom K)), hφ] at hh
  simpa only [coeff_sidePolynomial] using geometricApprox_balancedCutSums hI hh
    (r := splitWidth n (Fintype.card I) (Fintype.card J) s) le_rfl

/-- Pinning the program and taking its one-hot choices gives the complete splitting
step of §4.3 for a verified signed side program, including rejection of malformed rows. -/
theorem oneHot_balancedCutSums {P : Type*} [Fintype P]
    (layout : Fin n ≃ P ⊕ (I × J)) (pins : P → Bool) (A : (I → J) → ℤ)
    (correct : ∀ a, signedCount (oneHotWord layout pins a) = A a)
    (reject : ∀ x : Fin n → Bool, (∀ u, x (layout.symm (.inl u)) = pins u) →
      (¬ ∀ i, ∃! j, x (layout.symm (.inr (i,j))) = true) → signedCount x = 0)
    (hI : 3 ≤ Fintype.card I)
    (approx : geometricApprox n s (map (Int.castRingHom K) (Pstar n))) :
    (fun a => (A a : K)) ∈
      imageClosure (balancedCutSums I J K (splitWidth n (Fintype.card I) (Fintype.card J) s)) :=
  Pstar_projection_balancedCutSums _ _ (oneHotProjection_Pstar K layout pins A correct reject) hI approx

end Crossing

end BorderVNP
end Computability
end OAI
