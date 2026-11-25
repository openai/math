import OAI.Computability.BorderVNP.ResidueUniformizer
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian

/-! # Laurent expansion of functions on a discrete branch

Given the discrete valuation ring of a branch, pass to its actual adic completion.
The residue field is preserved by completion. Its coefficient section and the
uniformizer expansion identify the completed ring with power series. This yields
an embedding of the original function field in Laurent series over the original
residue field, taking every regular function to a series with the given residue.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue

open scoped PowerSeries
open IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- Completion in powers of the maximal ideal of the branch. -/
abbrev BranchCompletion (O : Type*) [CommRing O] [IsLocalRing O] :=
  AdicCompletion (maximalIdeal O) O

/-- Embedding the branch valuation ring in its completion is injective. -/
theorem toBranchCompletion_injective : Function.Injective (algebraMap O (BranchCompletion O)) := by
  have := IsHausdorff.of_isDomain (maximalIdeal O) (maximalIdeal.isMaximal O).ne_top
  exact AdicCompletion.of_injective _ _

private theorem trunc_residue {R k : Type*} [CommRing R] [CommRing k] (I : Ideal R)
    [IsAdicComplete I R] (rep : k →+* R) (s : R) (hs : s ∈ I) (f : k⟦X⟧) :
    Ideal.Quotient.mk I (uniformizerEval I rep s hs f) =
      Ideal.Quotient.mk I (rep (PowerSeries.coeff 0 f)) := by
  have h := uniformizerEval_mod I rep s hs 1 f
  simp only [PowerSeries.trunc_one_left, Polynomial.eval₂_C] at h
  have hm := Ideal.Quotient.eq.mp h
  rw [pow_one] at hm
  exact Ideal.Quotient.eq.mpr hm

variable (p : ℕ) [Fact p.Prime] [CharP O p] [CharP (ResidueField O) p]
  [Finite (ResidueField O)] (π : O) (hπ : Irreducible π)

include p hπ

/-- Completion preserves the residue field and sends the series variable to the uniformizer. -/
theorem exists_completionSeries :
    ∃ e : (ResidueField O)⟦X⟧ ≃+* BranchCompletion O,
      e PowerSeries.X = algebraMap O _ π ∧
      ∀ f, residue (BranchCompletion O) (e f) =
        ResidueField.map (algebraMap O _) (PowerSeries.coeff 0 f) := by
  let A := BranchCompletion O
  let I := maximalIdeal A
  let emb := algebraMap O A
  let r : ResidueField O ≃+* ResidueField A :=
    RingEquiv.ofBijective (ResidueField.map emb) (AdicCompletion.residueField_map_bijective O)
  let : CharP A p := charP_of_injective_ringHom (f := emb) toBranchCompletion_injective p
  let : CharP (ResidueField A) p := charP_of_injective_ringHom r.injective p
  let : Finite (ResidueField A) := Finite.of_surjective r r.surjective
  let : CharP (A ⧸ I) p := inferInstanceAs (CharP (ResidueField A) p)
  let : PerfectRing (A ⧸ I) p := inferInstanceAs (PerfectRing (ResidueField A) p)
  let rep := coefficientSection I p
  have hr := reduction_coefficientSection I p
  have gen : I = Ideal.span {emb π} := by
    calc
      I = (maximalIdeal O).map emb := AdicCompletion.maximalIdeal_eq_map
      _ = (Ideal.span {π}).map emb := congrArg (Ideal.map emb) hπ.maximalIdeal_eq
      _ = _ := by rw [Ideal.map_span, Set.image_singleton]
  have hs : emb π ∈ I := gen ▸ Ideal.mem_span_singleton_self _
  let F := uniformizerEval I rep (emb π) hs
  have inj : Function.Injective F := by
    let := Ideal.Quotient.field I
    apply (injective_iff_map_eq_zero _).mpr
    intro f hf
    by_contra h
    have he := congrArg F (PowerSeries.X_pow_order_mul_divXPowOrder (f := f))
    have hX : F PowerSeries.X = emb π := uniformizerEval_X _ _ _ _
    rw [map_mul, map_pow, hX, hf] at he
    have hzero := ((PowerSeries.isUnit_divided_by_X_pow_order h).map F).mul_left_eq_zero.mp he
    rw [← map_pow, ← map_zero emb] at hzero
    exact pow_ne_zero _ hπ.ne_zero (toBranchCompletion_injective hzero)
  let e := RingEquiv.ofBijective F ⟨inj, uniformizerEval_surjective I _ rep hr hs gen⟩
  let ρ := RingEquiv.ofBijective (PowerSeries.map r.toRingHom)
    ⟨PowerSeries.map_injective _ r.injective, PowerSeries.map_surjective _ r.surjective⟩
  refine ⟨ρ.trans e, ?_, ?_⟩
  · change F (PowerSeries.map r.toRingHom PowerSeries.X) = emb π
    rw [PowerSeries.map_X]
    exact uniformizerEval_X _ _ _ _
  · intro f
    change Ideal.Quotient.mk I (F (PowerSeries.map r.toRingHom f)) = r (PowerSeries.coeff 0 f)
    exact (trunc_residue I rep _ hs _).trans (hr _)

/-- Power-series presentation of the actual completion of the valuation ring. -/
noncomputable def completionSeries : (ResidueField O)⟦X⟧ ≃+* BranchCompletion O :=
  (exists_completionSeries p π hπ).choose

/-- Taylor expansion of a regular element, obtained from its image in the completion. -/
noncomputable def branchExpansion : O →+* (ResidueField O)⟦X⟧ :=
  (completionSeries p π hπ).symm.toRingHom.comp (algebraMap O _)

/-- No regular function disappears in its expansion. -/
theorem branchExpansion_injective : Function.Injective (branchExpansion p π hπ) :=
  (completionSeries p π hπ).symm.injective.comp toBranchCompletion_injective

/-- The constant term of a regular function's expansion is its residue. -/
theorem coeff_zero_branchExpansion (x : O) :
    PowerSeries.coeff 0 (branchExpansion p π hπ x) = residue O x := by
  apply (ResidueField.map (algebraMap O (BranchCompletion O))).injective
  rw [← (exists_completionSeries p π hπ).choose_spec.2, ResidueField.map_residue]
  change residue _ ((completionSeries p π hπ) ((completionSeries p π hπ).symm _)) = _
  rw [RingEquiv.apply_symm_apply]

/-- The chosen uniformizer expands as the series variable. -/
theorem branchExpansion_uniformizer : branchExpansion p π hπ π = PowerSeries.X :=
  (completionSeries p π hπ).injective <|
    ((completionSeries p π hπ).apply_symm_apply _).trans (exists_completionSeries p π hπ).choose_spec.1.symm

/-- Laurent expansion of an arbitrary rational function on the branch. -/
noncomputable def branchLaurentExpansion (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K] :
    K →+* LaurentSeries (ResidueField O) := IsFractionRing.map (branchExpansion_injective p π hπ)

/-- On the valuation ring the Laurent expansion agrees with its power-series expansion. -/
theorem branchLaurentExpansion_regular (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K]
    (x : O) : branchLaurentExpansion p π hπ K (algebraMap O K x) =
      algebraMap _ _ (branchExpansion p π hπ x) :=
  IsLocalization.map_eq (M := nonZeroDivisors O) (T := nonZeroDivisors (ResidueField O)⟦X⟧)
    (g := branchExpansion p π hπ)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (branchExpansion_injective p π hπ)) x

/-- The original function-field uniformizer expands as the monomial `s`. -/
theorem branchLaurentExpansion_uniformizer (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K] :
    branchLaurentExpansion p π hπ K (algebraMap O K π) = HahnSeries.single (1 : ℤ) 1 := by
  rw [branchLaurentExpansion_regular, branchExpansion_uniformizer]
  exact HahnSeries.ofPowerSeries_X

/-- A nonzero function vanishing at the point has strictly positive order
in the Laurent expansion at the chosen uniformizer. -/
theorem branchLaurentExpansion_pos (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K]
    (r : O) (hr : r ≠ 0) (hz : residue O r = 0) :
    0 < (branchLaurentExpansion p π hπ K (algebraMap O K r)).order := by
  let f := branchExpansion p π hπ r
  have hzero : PowerSeries.coeff 0 f = 0 := (coeff_zero_branchExpansion p π hπ r).trans hz
  have hf : f ≠ 0 := (map_ne_zero_iff _ (branchExpansion_injective p π hπ)).mpr hr
  rw [branchLaurentExpansion_regular]
  change 0 < (HahnSeries.ofPowerSeries ℤ _ f).order
  let y := HahnSeries.ofPowerSeries ℤ _ f
  have hy : y ≠ 0 := (map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).mpr hf
  by_contra! hn
  have hcoeff : y.coeff y.order ≠ 0 := HahnSeries.coeff_order_eq_zero.not.mpr hy
  rcases lt_or_eq_of_le hn with hlt | heq
  · exact hcoeff ((PowerSeries.coeff_coe f y.order).trans (ite_eq_left hlt))
  · rw [heq] at hcoeff
    exact hcoeff ((LaurentSeries.coeff_coe_powerSeries f 0).trans hzero)

end Residue

end BorderVNP
end Computability
end OAI
