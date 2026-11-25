import OAI.Computability.BorderVNP.ResidueApproximationMixed

/-! # Passing from `E(t)(x)` to the mixed residue test

The curve equations construct the root field over the fraction field of
`E[t]`. The mixed test uses the same field generated over `E` by `t` and the
root coordinates. This file verifies that passage and uses the actual
vanishing of `t` in the discrete valuation ring to produce the test.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue

open IsLocalRing
open scoped Polynomial

variable {E K ι : Type*} [Field E] [Field K] [Algebra E K] [Algebra E[X] K]
  [IsScalarTower E E[X] K] [Algebra (FractionRing E[X]) K] [IsScalarTower E[X] (FractionRing E[X]) K]

/-- Generators over the rational function field together with its parameter generate over `E`. -/
theorem parameter_adjoin_eq_top (x : ι → K)
    (hgen : IntermediateField.adjoin (FractionRing E[X]) (Set.range x) = ⊤) :
    IntermediateField.adjoin E (insert (algebraMap E[X] K Polynomial.X) (Set.range x)) = ⊤ := by
  let A := IntermediateField.adjoin E (insert (algebraMap E[X] K Polynomial.X) (Set.range x))
  have ht : algebraMap E[X] K Polynomial.X ∈ A := IntermediateField.subset_adjoin _ _ (by simp)
  have hpoly (g : E[X]) : algebraMap E[X] K g ∈ A := by
    induction g using Polynomial.induction_on' with
    | add a b ha hb => rw [map_add]; exact A.add_mem ha hb
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      exact A.mul_mem (by rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]; exact A.algebraMap_mem a)
        (A.toSubring.pow_mem ht n)
  have hrat (w : FractionRing E[X]) : algebraMap _ K w ∈ A := by
    obtain ⟨u, v, _, rfl⟩ := IsFractionRing.div_surjective E[X] w
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact A.div_mem (hpoly _) (hpoly _)
  let A' : IntermediateField (FractionRing E[X]) K := { A.toSubfield with algebraMap_mem' := hrat }
  have htop : ⊤ ≤ A' := by
    rw [← hgen, IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin E _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  exact top_unique fun z _ => htop (show z ∈ (⊤ : IntermediateField (FractionRing E[X]) K) from trivial)

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (p : ℕ) [Fact p.Prime] [CharP O p] [CharP (ResidueField O) p] [Finite (ResidueField O)]
  (π : O) (hπ : Irreducible π) [Algebra O K] [IsFractionRing O K]

attribute [local instance] branchPrimeAlgebra

/-- Trace-one mixed Laurent test for the parameter used by the actual algebraic root equations. -/
theorem parameter_trace_one_mixed [Fintype ι] (x : ι → K)
    (hgen : IntermediateField.adjoin (FractionRing E[X]) (Set.range x) = ⊤)
    (t : Kˣ) (ht : (t : K) = algebraMap E[X] K Polynomial.X)
    (u : O) (hu : algebraMap O K u = (t : K)) (hz : residue O u = 0)
    (η : LaurentSeries (ResidueField O)) (hη : η ≠ 0) :
    let ρ := branchLaurentExpansion p π hπ K
    ∃ f : Mixed ι E, tracedRes p (mixedEval (ρ.comp (algebraMap E K)) (ρ ∘ x)
      (Units.map ρ.toMonoidHom t) f * η) = 1 := by
  apply exists_trace_one_mixed p π hπ x t _ _ η hη
  · rw [ht]; exact parameter_adjoin_eq_top x hgen
  · rw [← hu]
    exact branchLaurentExpansion_pos p π hπ K u (fun h => t.ne_zero (hu.symm.trans (h ▸ map_zero _))) hz

end Residue

end BorderVNP
end Computability
end OAI
