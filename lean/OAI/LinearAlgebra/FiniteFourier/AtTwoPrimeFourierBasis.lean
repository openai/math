import OAI.LinearAlgebra.FiniteFourier.CyclicOrbitBasis
import OAI.LinearAlgebra.FiniteFourier.PrimeAxisAction
import OAI.LinearAlgebra.FiniteFourier.PrimeAxisCosets
import OAI.LinearAlgebra.FiniteFourier.PrimeAxisMonomials

/-! # Fourier eigenvectors on the signed prime-axis orbits

Reindex the nonzero monomials of the prime cyclotomic quotient by the two
cosets of squares. Fourier transformation on each coset gives a basis in
which the square generator acts diagonally and inversion exchanges the rows.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Module Polynomial
open scoped BigOperators

variable (R : Type*) [CommRing R] {p : ℕ} [Fact p.Prime] (C : PrimeAxisCosets p)

local notation "m" => (p - 1) / 2
local notation "A" => AdjoinRoot (cyclotomic p R)

/-- The two cycles of nonzero monomials, paired by inversion of the universal root. -/
noncomputable def atTwoPrimeMonomialBasis : Basis (Bool × Fin m) R A :=
  (primeAxisResidueBasis R p).reindex C.equiv.symm

theorem atTwoPrimeMonomialBasis_apply (c : Bool) (t : Fin m) :
    atTwoPrimeMonomialBasis R C (c,t) = primeAxisCharacter R p (C.equiv (c,t)) := by
  simp [atTwoPrimeMonomialBasis, primeAxisResidueBasis_apply]

/-- The frequency `j` Fourier vector supported on the square or nonsquare orbit. -/
noncomputable def atTwoPrimeFourier (u : Rˣ) (c : Bool) (j : Fin m) : A :=
  orbitFourier (atTwoPrimeMonomialBasis R C) u c j

private noncomputable def atTwoPrimeSeed (c : Bool) : A :=
  primeAxisCharacter R p (if c then -1 else 1)

private theorem atTwoPrimeOrbit (c : Bool) (t : Fin m) :
    ((primeAxisAction R p C.generator).toLinearMap ^ t.val) (atTwoPrimeSeed R c) =
      atTwoPrimeMonomialBasis R C (c,t) := by
  rw [← AlgEquiv.pow_toLinearMap, primeAxisAction_pow, atTwoPrimeMonomialBasis_apply]
  change primeAxisAction R p (C.generator ^ t.val) (primeAxisCharacter R p _) = _
  cases c <;> simp [C.equiv_false, C.equiv_true]

private theorem atTwoPrimeOrder :
    (primeAxisAction R p C.generator).toLinearMap ^ m = 1 := by
  rw [← AlgEquiv.pow_toLinearMap, primeAxisAction_pow, ← C.order_generator, pow_orderOf_eq_one]
  change ((primeAxisActionHom R p) 1).toLinearMap = _
  rw [map_one, AlgEquiv.one_toLinearMap]

variable (u : Rˣ)

/-- Multiplying exponents by the square generator acts diagonally on each row. -/
theorem atTwoPrimeFourier_eigen (hu : u ^ m = 1) (c : Bool) (j : Fin m) :
    primeAxisAction R p C.generator (atTwoPrimeFourier R C u c j) =
      (u : R)^j.val • atTwoPrimeFourier R C u c j :=
  orbitFourier_eigen _ _ _ hu (atTwoPrimeOrder R C) _ (atTwoPrimeOrbit R C) c j

/-- Inversion exchanges the two Fourier rows, preserving frequency. -/
theorem atTwoPrimeFourier_swap (c : Bool) (j : Fin m) :
    primeAxisAction R p (-1) (atTwoPrimeFourier R C u c j) =
      atTwoPrimeFourier R C u (!c) j := by
  apply map_orbitFourier (atTwoPrimeMonomialBasis R C) u (primeAxisAction R p (-1)).toLinearMap
  intro t
  simp only [atTwoPrimeMonomialBasis_apply, AlgEquiv.toLinearMap_apply, primeAxisAction_character]
  cases c <;> simp [C.equiv_false, C.equiv_true]

/-- The two Fourier rows together form a basis over the coefficient ring. -/
theorem exists_atTwoPrimeFourier_basis (hmpos : 0 < m) (hm : IsUnit ((m : ℕ) : R))
    (hu : u^m = 1) (hs : ∀ i j : Fin m, i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val)) :
    ∃ b : Basis (Bool × Fin m) R A, ∀ c j, b (c,j) = atTwoPrimeFourier R C u c j :=
  exists_orbitFourier_basis _ _ _ hmpos hm hu (atTwoPrimeOrder R C) hs _ (atTwoPrimeOrbit R C)

/-- Each eigenspace is spanned by the pair of rows at that frequency. -/
theorem atTwoPrimeFourier_eigenspace (hmpos : 0 < m) (hm : IsUnit ((m : ℕ) : R))
    (hu : u^m = 1) (hs : ∀ i j : Fin m, i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val))
    (j : Fin m) :
    Module.End.eigenspace (primeAxisAction R p C.generator).toLinearMap ((u:R)^j.val) =
      Submodule.span R (Set.range (fun c => atTwoPrimeFourier R C u c j)) :=
  eigenspace_eq_span_orbitFourier _ _ _ hmpos hm hu (atTwoPrimeOrder R C) hs _ (atTwoPrimeOrbit R C) j

/-- At frequency zero, the square row is the positive quadratic period. -/
theorem atTwoPrimeFourier_false_zero (hmpos : 0 < m) :
    atTwoPrimeFourier R C u false ⟨0,hmpos⟩ = quadraticPeriod (primeAxisCharacter R p) 1 := by
  classical
  simp only [atTwoPrimeFourier, orbitFourier, pow_zero, inv_one, Units.val_one, one_pow,
    one_smul, atTwoPrimeMonomialBasis_apply, quadraticPeriod_eq_sum]
  let e (t : Fin m) : ZMod p := C.equiv (false,t)
  have he : Function.Injective e := fun i j h =>
    congrArg Prod.snd (C.equiv.injective (Units.ext h))
  apply Fintype.sum_of_injective e he
  · intro x hx
    apply ite_eq_right
    intro hχ
    have hzero : x ≠ 0 := by rintro rfl; simp at hχ
    obtain ⟨⟨c,t⟩,ht⟩ := C.equiv.surjective (Units.mk0 x hzero)
    have hsign := C.isSquare_coe_equiv_iff (c,t)
    rw [ht] at hsign
    have hc : c = false := hsign.mp ((quadraticChar_one_iff_isSquare hzero).mp hχ)
    subst c
    exact hx ⟨t,congrArg Units.val ht⟩
  · intro t
    have hχ := (quadraticChar_one_iff_isSquare (C.equiv (false,t)).ne_zero).mpr
      ((C.isSquare_coe_equiv_iff (false,t)).mpr rfl)
    simp [e, hχ]

/-- At frequency zero, the nonsquare row is the negative quadratic period. -/
theorem atTwoPrimeFourier_true_zero (hp : p % 4 = 3) (hmpos : 0 < m) :
    atTwoPrimeFourier R C u true ⟨0,hmpos⟩ = quadraticPeriod (primeAxisCharacter R p) (-1) := by
  rw [← primeAxisAction_neg_period R p hp 1, ← atTwoPrimeFourier_false_zero R C u hmpos,
    atTwoPrimeFourier_swap]
  rfl

end FiniteFourier
end LinearAlgebra
end OAI
