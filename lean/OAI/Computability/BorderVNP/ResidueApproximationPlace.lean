import OAI.Computability.BorderVNP.ResidueApproximation
import OAI.Computability.BorderVNP.ResidueCompletion
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # A polynomial test of absolute residue one

At the chosen branch, multiply a lift of a suitable residue by an integral
power of its uniformizer. Against a nonzero test differential this attains
any prescribed residue. Laurent-polynomial approximation of the resulting
rational function preserves the residue and supplies the test of Section 10.2.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue

open HahnSeries IsLocalRing
open scoped PowerSeries

private theorem res_shift_regular {κ : Type*} [Field κ] (η : LaurentSeries κ) (w : κ⟦X⟧) :
    res (single (-1 - η.order) (1 : κ) * ofPowerSeries ℤ κ w * η) =
      PowerSeries.coeff 0 w * η.leadingCoeff := by
  let v := η.order
  have he : single (-1 - v) (1 : κ) * ofPowerSeries ℤ κ w * η =
      single (-1 : ℤ) 1 * ofPowerSeries ℤ κ (w * η.powerSeriesPart) := by
    calc
      _ = single (-1 - v) (1 : κ) * ofPowerSeries ℤ κ w *
            (single v 1 * ofPowerSeries ℤ κ η.powerSeriesPart) := by
              rw [LaurentSeries.single_order_mul_powerSeriesPart]
      _ = (single (-1 - v) (1 : κ) * single v 1) *
            (ofPowerSeries ℤ κ w * ofPowerSeries ℤ κ η.powerSeriesPart) := by ring
      _ = _ := by rw [single_mul_single, sub_add_cancel, one_mul, map_mul]
  rw [he, res, coeff_single_mul, sub_self, one_mul,
    show (0 : ℤ) = ↑(0 : ℕ) by rfl, LaurentSeries.coeff_coe_powerSeries,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    LaurentSeries.powerSeriesPart_coeff, Nat.cast_zero, add_zero, leadingCoeff_eq]

variable {O K E ι : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (p : ℕ) [Fact p.Prime] [CharP O p] [CharP (ResidueField O) p] [Finite (ResidueField O)]
  (π : O) (hπ : Irreducible π) [Field K] [Algebra O K] [IsFractionRing O K]
  [Field E] [Algebra E K]

/-- Any residue is attained against a nonzero differential by a function
in the original function field of the branch. -/
theorem exists_function_residue (η : LaurentSeries (ResidueField O)) (hη : η ≠ 0)
    (c : ResidueField O) : ∃ z : K, res (branchLaurentExpansion p π hπ K z * η) = c := by
  obtain ⟨w, hw⟩ := residue_surjective (c / η.leadingCoeff)
  let ρ := branchLaurentExpansion p π hπ K
  have hvar : ρ (algebraMap O K π) = single 1 1 := by
    change branchLaurentExpansion p π hπ K _ = _
    rw [branchLaurentExpansion_regular, branchExpansion_uniformizer]
    exact ofPowerSeries_X
  refine ⟨algebraMap O K π ^ (-1 - η.order) * algebraMap O K w, ?_⟩
  change res (ρ (_ * _) * _) = _
  rw [map_mul, map_zpow₀, hvar, ← RatFunc.single_zpow,
    show ρ (algebraMap O K w) = ofPowerSeries ℤ _ (branchExpansion p π hπ w) from
      branchLaurentExpansion_regular p π hπ K w,
    res_shift_regular, coeff_zero_branchExpansion, hw, div_mul_cancel₀ _ (leadingCoeff_eq_zero.not.mpr hη)]

/-- Canonical prime-field structure on the residue field of the branch. -/
@[instance_reducible] noncomputable def branchPrimeAlgebra : Algebra (ZMod p) (ResidueField O) := ZMod.algebra _ _

attribute [local instance] branchPrimeAlgebra

/-- Over the function field `E(t,x)`, an actual polynomial in `x,t,t⁻¹` attains
absolute trace one against any nonzero differential at the chosen finite place. -/
theorem exists_trace_one_polynomial (x : ι → K) (t : K)
    (hgen : IntermediateField.adjoin E (insert t (Set.range x)) = ⊤)
    (ht : 0 < (branchLaurentExpansion p π hπ K t).order)
    (η : LaurentSeries (ResidueField O)) (hη : η ≠ 0) :
    let ρ := branchLaurentExpansion p π hπ K
    ∃ f : MvPolynomial (ι ⊕ Bool) E, tracedRes p
      (MvPolynomial.eval₂ (ρ.comp (algebraMap E K)) (branchCoordinates (ρ ∘ x) (ρ t)) f * η) = 1 := by
  classical
  let κ := ResidueField O
  let := Fintype.ofFinite κ
  let ρ := branchLaurentExpansion p π hπ K
  let : Algebra E (LaurentSeries κ) := (ρ.comp (algebraMap E K)).toAlgebra
  let φ : K →ₐ[E] LaurentSeries κ := ⟨ρ, fun _ => rfl⟩
  let A := IntermediateField.adjoin E (Set.range (branchCoordinates (ρ ∘ x) (ρ t)))
  have hincl : (⊤ : IntermediateField E K) ≤ A.comap φ := by
    rw [← hgen, IntermediateField.adjoin_le_iff]
    rintro y (hy | ⟨i, rfl⟩)
    · subst y; exact IntermediateField.subset_adjoin E _ ⟨Sum.inr true, rfl⟩
    · exact IntermediateField.subset_adjoin E _ ⟨Sum.inl i, rfl⟩
  obtain ⟨c, hc⟩ := Algebra.trace_surjective (ZMod p) κ 1
  obtain ⟨z, hz⟩ := exists_function_residue (K := K) p π hπ η hη c
  have hmem : ρ z ∈ A := hincl (show z ∈ (⊤ : IntermediateField E K) from trivial)
  obtain ⟨f, hf⟩ := exists_residue_polynomial (E := E) (ρ ∘ x) ht hmem η
  refine ⟨f, ?_⟩
  change Algebra.trace (ZMod p) κ (res (MvPolynomial.aeval (branchCoordinates (ρ ∘ x) (ρ t)) f * η)) = 1
  rw [hf, hz, hc]

end Residue

end BorderVNP
end Computability
end OAI
