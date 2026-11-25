import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# A horizontal component through an isolated special-fiber point

At the isolated point of (9.1), the local height exceeds the number of
deformation equations. A minimal prime of the equations below that point
is horizontal, and the point has height exactly one on this component.
This is the local Krull dimension argument in the proof of Proposition 9.2.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

/-- The component through an isolated special-fiber point has a nonvanishing
parameter and local dimension one, provided the ambient local dimension is
larger than the number of equations. -/
theorem exists_horizontal_component {R : Type*} [CommRing R] [IsNoetherianRing R]
    (eqns : Finset R) (t : R) (m : Ideal R)
    (isolated : m ∈ (Ideal.span (eqns : Set R) ⊔ Ideal.span {t}).minimalPrimes)
    (dimension : (eqns.card : ℕ∞) < m.height) :
    ∃ P ∈ (Ideal.span (eqns : Set R)).minimalPrimes, P < m ∧ t ∉ P ∧
      (m.map (Ideal.Quotient.mk P)).height = 1 := by
  let I := Ideal.span (eqns : Set R)
  have : m.IsPrime := isolated.isPrime
  obtain ⟨P, hP, hPm⟩ := Ideal.exists_minimalPrimes_le (I := I)
    (le_sup_left.trans isolated.le)
  have : P.IsPrime := hP.isPrime
  have hlt : P < m := lt_of_le_of_ne hPm (fun e => by
    have bound := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hP
    exact dimension.not_ge (e ▸ bound))
  have htP : t ∉ P := fun ht => hlt.not_ge (isolated.2
    ⟨hP.isPrime, sup_le hP.le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ht))⟩ hPm)
  have hiso : m ∈ (P ⊔ Ideal.span {t}).minimalPrimes := by
    refine ⟨⟨isolated.isPrime, sup_le hPm (le_sup_right.trans isolated.le)⟩, ?_⟩
    intro Q hQ hQm
    exact isolated.2 ⟨hQ.1, (sup_le_sup_right hP.le _).trans hQ.2⟩ hQm
  have hne : m.map (Ideal.Quotient.mk P) ≠ ⊥ := by
    rw [ne_eq, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact hlt.not_ge
  refine ⟨P, hP, hlt, htP, le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hiso) ?_⟩
  exact Order.one_le_iff_ne_zero.mpr (mt Ideal.height_eq_zero_iff_eq_bot.mp hne)

/-- A nonzero parameter vanishing at a point of an integral component gives a
dominant map from the component to the affine line over the ground field. -/
theorem parameter_dominant {K A : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (t : A) (ht : t ≠ 0) (point : Ideal A) (proper : point ≠ ⊤) (at_zero : t ∈ point) :
    Function.Injective (Polynomial.aeval (R := K) t) :=
  transcendental_iff_injective.mp fun h =>
    proper (point.eq_top_of_isUnit_mem at_zero (h.isIntegral.isUnit ht))

end Branch

end BorderVNP
end Computability
end OAI
