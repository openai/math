import OAI.Computability.BorderVNP.DecisionRecipe
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-! # Finite component decomposition in affine recipe coordinates

Minimal primes describe the irreducible components of the zero set over
an algebraically closed field. Their finite number need not be charged in
the largest individual recipe size.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Decision
open MvPolynomial

variable {K : Type*} [Field K] {I : Type}

/-- Every zero locus is already closed under the affine image closure. -/
theorem imageClosure_zeroLocus (J : Ideal (MvPolynomial I K)) :
    imageClosure (zeroLocus K J) = zeroLocus K J :=
  Set.Subset.antisymm (zeroLocus_anti_mono (le_vanishingIdeal_zeroLocus J)) (subset_imageClosure _)

/-- The zero set of a minimal prime is a maximal irreducible closed piece. -/
theorem component_of_minimalPrime [IsAlgClosed K] [Finite I] {J P : Ideal (MvPolynomial I K)}
    (h : P ∈ J.minimalPrimes) : IsComponent (zeroLocus K P) (zeroLocus K J) := by
  have : P.IsPrime := h.isPrime
  refine ⟨zeroLocus_anti_mono h.le, imageClosure_zeroLocus _, ?_, ?_⟩
  · rw [irreducible_iff_prime, IsPrime.vanishingIdeal_zeroLocus]
    exact h.isPrime
  · intro D hDJ _ hirr hPD
    have prime := (irreducible_iff_prime D).mp hirr
    have below := vanishingIdeal_anti_mono (k := K) hPD
    rw [IsPrime.vanishingIdeal_zeroLocus] at below
    apply le_zeroLocus_iff_le_vanishingIdeal.mpr
    exact h.2 ⟨prime, le_zeroLocus_iff_le_vanishingIdeal.mp hDJ⟩ below

/-- At every point of the zero set, choose a minimal prime beneath the prime
ideal of the point. The resulting pieces form a finite cover. -/
theorem zeroLocus_eq_union_components [IsAlgClosed K] [Finite I] (J : Ideal (MvPolynomial I K)) :
    ∃ c : Finset (Set (I → K)), zeroLocus K J = ⋃₀ (c : Set (Set (I → K))) ∧
      ∀ V ∈ c, IsComponent V (zeroLocus K J) := by
  classical
  let P := (J.finite_minimalPrimes_of_isNoetherianRing _).toFinset
  let c := P.image (zeroLocus K)
  have hcomp {V} (h : V ∈ c) : IsComponent V (zeroLocus K J) := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    exact component_of_minimalPrime (by simpa [P] using hp)
  refine ⟨c, Set.Subset.antisymm ?_ ?_, fun V h => hcomp h⟩
  · intro x hx
    let m := vanishingIdeal K ({x} : Set (I → K))
    have : m.IsPrime := inferInstanceAs (vanishingIdeal K ({x} : Set (I → K))).IsPrime
    have hJm : J ≤ m := fun p hp y hy => (Set.mem_singleton_iff.mp hy).symm ▸ hx p hp
    obtain ⟨p, hp, hm⟩ := Ideal.exists_minimalPrimes_le hJm
    exact ⟨zeroLocus K p, Finset.mem_image_of_mem _ (by simpa [P] using hp),
      fun r hr => hm hr _ (Set.mem_singleton x)⟩
  · rintro x ⟨V, hV, hx⟩
    exact (hcomp hV).1 hx

/-- Every affine closed set is a finite union of its irreducible components. -/
theorem closed_eq_union_components [IsAlgClosed K] [Finite I] {S : Set (I → K)}
    (h : imageClosure S = S) : ∃ c : Finset (Set (I → K)), S = ⋃₀ (c : Set (Set (I → K))) ∧
      ∀ V ∈ c, IsComponent V S := by
  rw [← h, imageClosure_eq_zeroLocus]
  exact zeroLocus_eq_union_components _

end Decision

end BorderVNP
end Computability
end OAI
