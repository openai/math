import OAI.LinearAlgebra.FiniteFourier.CyclicOrbitBasis
import OAI.LinearAlgebra.FiniteFourier.PrimeAxisAction
import OAI.LinearAlgebra.FiniteFourier.PrimeAxisMonomials

/-! # Rader coordinates on the full orbit of nonzero residues

The cyclic group of unit residues acts transitively on the positive-power basis of
the prime cyclotomic quotient. Fourier transformation of that orbit diagonalizes
the generator over every coefficient ring with unit differences of the nodes.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Module Polynomial Submodule
open scoped BigOperators

variable {p : ℕ} [hp : Fact p.Prime]

/-- A primitive residue lists every nonzero exponent once. -/
structure PrimeAxisOrbit (p : ℕ) where
  generator : (ZMod p)ˣ
  order_generator : orderOf generator = p - 1
  equiv : Fin (p-1) ≃ (ZMod p)ˣ
  equiv_apply (t : Fin (p-1)) : equiv t = generator ^ t.val

def PrimeAxisOrbit.ofPrime (p : ℕ) [hp : Fact p.Prime] : PrimeAxisOrbit p := by
  classical
  let g := (IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)).choose
  have hg : orderOf g = Nat.card (ZMod p)ˣ := IsCyclic.exists_ofOrder_eq_natCard.choose_spec
  have hc : Fintype.card (ZMod p)ˣ = p - 1 := (Nat.prime_iff_card_units p).mp hp.out
  rw [Nat.card_eq_fintype_card, hc] at hg
  let f (i : Fin (p-1)) := g ^ i.val
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (hg.symm ▸ i.isLt) (hg.symm ▸ j.isLt) hij
  exact ⟨g, hg, Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2
    ⟨hf, by simp [hc]⟩), fun _ => rfl⟩

variable (R : Type*) [CommRing R] (C : PrimeAxisOrbit p)
local notation "m" => (p - 1)
local notation "A" => AdjoinRoot (cyclotomic p R)

private def dyadicOrbitIndex : Unit × Fin m ≃ (ZMod p)ˣ := (Equiv.punitProd _).trans C.equiv

/-- The orbit is indexed as a singleton family for use with the cyclic Fourier basis. -/
def dyadicPrimeOrbitBasis : Basis (Unit × Fin m) R A :=
  (primeAxisResidueBasis R p).reindex (dyadicOrbitIndex C).symm

theorem dyadicPrimeOrbitBasis_apply (t : Fin m) :
    dyadicPrimeOrbitBasis R C ((), t) = primeAxisCharacter R p (C.equiv t) := by
  simp [dyadicPrimeOrbitBasis, dyadicOrbitIndex, primeAxisResidueBasis_apply]

private theorem dyadicPrimeOrbit (c : Unit) (t : Fin m) :
    ((primeAxisAction R p C.generator).toLinearMap ^ t.val) (primeAxisCharacter R p 1) =
      dyadicPrimeOrbitBasis R C (c,t) := by
  cases c
  rw [← AlgEquiv.pow_toLinearMap, primeAxisAction_pow, dyadicPrimeOrbitBasis_apply]
  change primeAxisAction R p _ (primeAxisCharacter R p _) = _
  simp [C.equiv_apply]

private theorem dyadicPrimeOrder :
    (primeAxisAction R p C.generator).toLinearMap ^ m = 1 := by
  rw [← AlgEquiv.pow_toLinearMap, primeAxisAction_pow, ← C.order_generator, pow_orderOf_eq_one]
  change ((primeAxisActionHom R p) 1).toLinearMap = _
  rw [map_one, AlgEquiv.one_toLinearMap]

variable (u : Rˣ)

/-- Lagrange resolvent for the character of the unit group indexed by `j`. -/
def dyadicPrimeFourier (j : Fin m) : A := orbitFourier (dyadicPrimeOrbitBasis R C) u () j

theorem dyadicPrimeFourier_eigen (hu : u^m = 1) (j : Fin m) :
    primeAxisAction R p C.generator (dyadicPrimeFourier R C u j) =
      (u : R)^j.val • dyadicPrimeFourier R C u j :=
  orbitFourier_eigen _ _ _ hu (dyadicPrimeOrder R C) _ (dyadicPrimeOrbit R C) () j

theorem exists_dyadicPrimeFourier_basis (hm : IsUnit ((m : ℕ) : R))
    (hu : u^m = 1) (hs : ∀ i j : Fin m, i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val)) :
    ∃ b : Basis (Fin m) R A, ∀ j, b j = dyadicPrimeFourier R C u j := by
  have hmpos : 0 < m := by have := hp.out.two_le; omega
  obtain ⟨b,hb⟩ := exists_orbitFourier_basis _ _ _ hmpos hm hu (dyadicPrimeOrder R C) hs
    _ (dyadicPrimeOrbit R C)
  exact ⟨b.reindex (Equiv.punitProd _), fun j => (Basis.reindex_apply ..).trans (hb () j)⟩

theorem dyadicPrimeFourier_eigenspace (hm : IsUnit ((m : ℕ) : R))
    (hu : u^m = 1) (hs : ∀ i j : Fin m, i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val)) (j : Fin m) :
    Module.End.eigenspace (primeAxisAction R p C.generator).toLinearMap ((u:R)^j.val) =
      span R {dyadicPrimeFourier R C u j} := by
  have hmpos : 0 < m := by have := hp.out.two_le; omega
  rw [eigenspace_eq_span_orbitFourier _ _ _ hmpos hm hu (dyadicPrimeOrder R C) hs _
    (dyadicPrimeOrbit R C) j]
  congr 1
  ext x
  change (∃ c : Unit, _ = x) ↔ x = _
  constructor
  · rintro ⟨⟨⟩, rfl⟩; rfl
  · rintro rfl; exact ⟨(),rfl⟩

theorem dyadicPrimeFourier_zero (hmpos : 0 < m) :
    dyadicPrimeFourier R C u ⟨0, hmpos⟩ = -1 := by
  classical
  simp only [dyadicPrimeFourier, orbitFourier, pow_zero, inv_one, Units.val_one, one_pow,
    one_smul, dyadicPrimeOrbitBasis_apply]
  rw [C.equiv.sum_comp (fun a : (ZMod p)ˣ => primeAxisCharacter R p a)]
  have h := Fintype.sum_eq_add_sum_subtype_ne (fun a => primeAxisCharacter R p a) (0 : ZMod p)
  rw [primeAxisCharacter_sum] at h
  rw [← (unitsEquivNeZero (G₀ := ZMod p)).sum_comp] at h
  simpa using eq_neg_of_add_eq_zero_left (show (∑ i : (ZMod p)ˣ, primeAxisCharacter R p i) + 1 = 0 by
    simpa [add_comm] using h.symm)


/-- Inverse orbit expansion. Only a Fourier matrix and the common scalar
`1 / (p-1)` occur in the coordinates of a nonzero input monomial. -/
theorem dyadicPrimeOrbit_fourierExpansion (hm : IsUnit ((m : ℕ) : R))
    (hu : u^m = 1) (hs : ∀ i j : Fin m, i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val))
    (t : Fin m) :
    primeAxisCharacter R p (C.equiv t) =
      ∑ j : Fin m, ((↑hm.unit⁻¹ : R) * (u:R)^(j.val * t.val)) • dyadicPrimeFourier R C u j := by
  let σ := (primeAxisAction R p C.generator).toLinearMap
  let v := primeAxisCharacter R p 1
  have hbase := LinearMap.congr_fun (sum_cyclicProjector σ u
    (by have := hp.out.two_le; omega : 0 < m) hu hm hs) v
  have hsums (j : Fin m) : cyclicSpectralSum σ u m j.val v = dyadicPrimeFourier R C u j :=
    (orbitFourier_eq_sum _ _ σ _ (dyadicPrimeOrbit R C) () j).symm
  simp only [LinearMap.sum_apply, cyclicProjector, LinearMap.smul_apply, hsums,
    Module.End.one_apply] at hbase
  have hpow (j : Fin m) (k : ℕ) :
      (σ^k) (dyadicPrimeFourier R C u j) = (u:R)^(j.val*k) • dyadicPrimeFourier R C u j := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul]
      change _ • primeAxisAction R p C.generator _ = _
      rw [dyadicPrimeFourier_eigen R C u hu, smul_smul, ← pow_add, Nat.mul_succ]
  rw [← dyadicPrimeOrbitBasis_apply, ← dyadicPrimeOrbit R C () t]
  change (σ^t.val) v = _
  rw [← hbase, map_sum]
  simp only [map_smul, hpow, smul_smul]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
