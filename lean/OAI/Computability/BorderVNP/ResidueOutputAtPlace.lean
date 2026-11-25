import OAI.Computability.BorderVNP.ResidueOutputSpecialization
import OAI.Computability.BorderVNP.ResidueCompletion
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Reading prime-field boundary coordinates in the completed place

A regular coordinate which differs from a prime-field scalar by a nonunit at
the selected place has exactly that scalar as its Laurent constant coefficient.
This converts the output condition of Proposition 9.2 to the hypotheses of
the polynomial specialization and pin lemmas.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue

open IsLocalRing HahnSeries MvPolynomial

variable {K : Type*} [Field K] (V : ValuationSubring K) [IsDiscreteValuationRing V]
  (p : ℕ) [Fact p.Prime] [CharP V p] [CharP (ResidueField V) p]
  [Finite (ResidueField V)] [Algebra (ZMod p) K] [Algebra (ZMod p) (ResidueField V)]
  (s : V) (hs : Irreducible s)

/-- Regularity and value of a coefficient on the branch, expressed directly in
the Laurent completion used by the pin tests. -/
theorem completed_prime_output {y : K} (z : ZMod p) (hy : y ∈ V)
    (hz : y - algebraMap (ZMod p) K z ∈ V.nonunits) :
    let ρ := branchLaurentExpansion p s hs K
    0 ≤ (ρ y).order ∧ (ρ y).coeff 0 = algebraMap (ZMod p) (ResidueField V) z := by
  let φ : ZMod p →+* V := ZMod.castHom (by rfl) V
  have hK : V.subtype.comp φ = algebraMap (ZMod p) K := RingHom.ext_zmod _ _
  have hκ : (residue V).comp φ = algebraMap (ZMod p) (ResidueField V) := RingHom.ext_zmod _ _
  let b : V := ⟨y, hy⟩
  have hb : b - φ z ∈ maximalIdeal V := by
    apply V.coe_mem_nonunits_iff.mp
    change y - (V.subtype.comp φ) z ∈ V.nonunits
    rwa [hK]
  have hres := (residue_eq_zero_iff _).mpr hb
  rw [map_sub, sub_eq_zero] at hres
  have he : branchLaurentExpansion p s hs K y =
      ofPowerSeries ℤ (ResidueField V) (branchExpansion p s hs b) :=
    branchLaurentExpansion_regular p s hs K b
  dsimp only
  rw [he]
  refine ⟨ofPowerSeries_nonnegative _, ?_⟩
  have hcoeff := ofPowerSeries_apply_coeff (Γ := ℤ) (branchExpansion p s hs b) 0
  rw [coeff_zero_branchExpansion, hres] at hcoeff
  exact hcoeff.trans (RingHom.congr_fun hκ z)

/-- The same completion evaluates the integer parse table, including coefficients
with repeated variables. -/
theorem completed_table_outputs {σ ι : Type*} (x : σ → K)
    (Y : ι → MvPolynomial σ ℤ) (c : ι → ZMod p)
    (hy : ∀ i, eval₂ (Int.castRingHom K) x (Y i) ∈ V)
    (hc : ∀ i, eval₂ (Int.castRingHom K) x (Y i) - algebraMap (ZMod p) K (c i) ∈ V.nonunits) :
    let ρ := branchLaurentExpansion p s hs K
    ∀ i, let y := eval₂ (Int.castRingHom (LaurentSeries (ResidueField V))) (ρ ∘ x) (Y i)
         0 ≤ y.order ∧ y.coeff 0 = algebraMap (ZMod p) (ResidueField V) (c i) := by
  intro ρ i
  have h := completed_prime_output V p s hs (c i) (hy i) (hc i)
  change 0 ≤ (ρ ((eval₂Hom (Int.castRingHom K) x) (Y i))).order ∧
    (ρ ((eval₂Hom (Int.castRingHom K) x) (Y i))).coeff 0 = _ at h
  rw [map_eval₂Hom, Subsingleton.elim (ρ.comp (Int.castRingHom K)) (Int.castRingHom _)] at h
  exact h

end Residue

end BorderVNP
end Computability
end OAI
