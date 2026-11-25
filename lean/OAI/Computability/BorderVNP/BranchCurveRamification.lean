import OAI.Computability.BorderVNP.BranchCurveLaurentOrder
import OAI.Computability.BorderVNP.ResidueCompletion
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Ramification bounded by the degree of the arithmetic function field

In the actual Laurent expansion at the discrete place, the order of every
nonzero element of the parameter field is a multiple of the order of `t`.
The first `ord(t)` powers of a uniformizer therefore have distinct orders
modulo this integer, and are linearly independent over the parameter field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open HahnSeries
open scoped LaurentSeries

/-- Orders of nonzero rational functions in the parameter are multiples of
its positive Laurent order. -/
theorem parameter_order_dvd_rational_order {E κ : Type*} [Field E] [Finite E] [Field κ]
    (φ : E →+* LaurentSeries κ) (τ : LaurentSeries κ) (ht : 0 < τ.order)
    (f : FractionRing (Polynomial E) →+* LaurentSeries κ)
    (hf : ∀ p : Polynomial E, f (algebraMap _ _ p) = p.eval₂ φ τ)
    (a : FractionRing (Polynomial E)) (ha : a ≠ 0) : τ.order ∣ (f a).order := by
  obtain ⟨p, q, hq, he⟩ := IsFractionRing.div_surjective (Polynomial E) a
  have hp : p ≠ 0 := fun hz => ha (by simpa [hz] using he.symm)
  have hq' := mem_nonZeroDivisors_iff_ne_zero.mp hq
  have hp' := order_eval₂_at_positive_parameter φ τ ht p hp
  have hq'' := order_eval₂_at_positive_parameter φ τ ht q hq'
  have hmul : f a * q.eval₂ φ τ = p.eval₂ φ τ := by
    rw [← he, map_div₀, hf, hf, div_mul_cancel₀ _ hq''.1]
  have eo := congrArg HahnSeries.order hmul
  rw [order_mul ((map_ne_zero_iff _ f.injective).mpr ha) hq''.1, hp'.2, hq''.2] at eo
  exact ⟨(p.natTrailingDegree : ℤ) - q.natTrailingDegree, by linarith⟩

/-- A uniformizer has the first `e` powers linearly independent if all
nonzero base field elements have order divisible by `e`. -/
theorem ramification_le_finrank {F L κ : Type*} [Field F] [Field L] [Algebra F L] [Field κ]
    [FiniteDimensional F L] (f : L →+* LaurentSeries κ) (e : ℕ)
    (base_order : ∀ a : F, a ≠ 0 → (e : ℤ) ∣ (f (algebraMap F L a)).order)
    (s : L) (hs : (f s).order = 1) : e ≤ Module.finrank F L := by
  classical
  have hfs : f s ≠ 0 := fun hz => by simp [hz] at hs
  have hli : LinearIndependent F (fun i : Fin e => s ^ (i : ℕ)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro a he i
    by_contra hi
    let S := Finset.univ.filter (fun j => a j ≠ 0)
    let term := fun j : Fin e => f (a j • s ^ (j : ℕ))
    have ha j (hj : j ∈ S) : a j ≠ 0 := (Finset.mem_filter.mp hj).2
    have nz j (hj : j ∈ S) : term j ≠ 0 := by
      simp only [term, Algebra.smul_def, map_mul, map_pow]
      exact mul_ne_zero ((map_ne_zero_iff _ f.injective).mpr ((map_ne_zero_iff _ (algebraMap F L).injective).mpr (ha j hj)))
        (pow_ne_zero _ hfs)
    have ho j (hj : j ∈ S) : (term j).order % e = (j.val : ℤ) := by
      have hn : f (algebraMap F L (a j)) ≠ 0 := (map_ne_zero_iff _ f.injective).mpr
        ((map_ne_zero_iff _ (algebraMap F L).injective).mpr (ha j hj))
      simp only [term, Algebra.smul_def, map_mul, map_pow, order_mul hn (pow_ne_zero _ hfs),
        order_pow, hs, mul_one]
      rw [Int.add_emod, Int.emod_eq_zero_of_dvd (base_order _ (ha _ hj)), zero_add, Int.emod_emod]
      change (j.val : ℤ) % (e : ℤ) = _
      exact Int.emod_eq_of_lt (Int.natCast_nonneg j.val) (by exact_mod_cast j.isLt)
    obtain ⟨j, hj, hmin⟩ := S.exists_min_image (fun j => (term j).order)
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    have strict k (hk : k ∈ S) (hkj : k ≠ j) : (term j).order < (term k).order := by
      apply lt_of_le_of_ne (hmin k hk)
      intro eq
      have hv : (j.val : ℤ) = k.val := (ho j hj).symm.trans
        ((congrArg (fun n : ℤ => n % e) eq).trans (ho k hk))
      exact hkj (Fin.ext (by exact_mod_cast hv.symm))
    apply (order_sum_of_unique_min S term j hj (nz _ hj) strict).1
    calc
      ∑ j ∈ S, term j = ∑ j, term j := Finset.sum_subset (Finset.filter_subset _ _) (fun k _ h => by
        have hk : a k = 0 := by simpa [S] using h
        simp [term, hk])
      _ = 0 := (map_sum f _ _).symm.trans ((congrArg f he).trans (map_zero f))
  simpa using hli.fintype_card_le_finrank

/-- The Laurent expansion of the actual DVR uniformizer has order one. -/
theorem normalized_uniformizer_order {O L : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (p : ℕ) [Fact p.Prime] [CharP O p] [CharP (IsLocalRing.ResidueField O) p]
    [Finite (IsLocalRing.ResidueField O)] (s : O) (hs : Irreducible s) :
    (Residue.branchLaurentExpansion p s hs L (algebraMap O L s)).order = 1 := by
  rw [Residue.branchLaurentExpansion_regular, Residue.branchExpansion_uniformizer]
  exact (congrArg HahnSeries.order PowerSeries.coe_X).trans (order_single one_ne_zero)

/-- A nonzero regular function vanishing at the residue point has positive
order in the actual completed uniformizer expansion. -/
theorem positive_order_at_zero {O L : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (p : ℕ) [Fact p.Prime] [CharP O p] [CharP (IsLocalRing.ResidueField O) p]
    [Finite (IsLocalRing.ResidueField O)] (s : O) (hs : Irreducible s)
    (a : O) (ha : a ≠ 0) (hzero : IsLocalRing.residue O a = 0) :
    0 < (Residue.branchLaurentExpansion p s hs L (algebraMap O L a)).order := by
  let w := Residue.branchExpansion p s hs a
  have hw : w ≠ 0 := (map_ne_zero_iff _ (Residue.branchExpansion_injective p s hs)).mpr ha
  have hn : HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField O) w ≠ 0 :=
    (map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).mpr hw
  rw [Residue.branchLaurentExpansion_regular]
  change 0 < (HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField O) w).order
  by_contra! h
  apply (coeff_order_eq_zero.not.mpr hn)
  rw [PowerSeries.coeff_coe]
  split_ifs with hl
  · rfl
  · have h0 : (HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField O) w).order = 0 :=
      le_antisymm h (le_of_not_gt hl)
    simp only [h0, Int.natAbs_zero]
    exact (Residue.coeff_zero_branchExpansion p s hs a).trans hzero

/-- The Laurent order of the parameter in the actual completion is positive
and bounded by the degree of the arithmetic function field over `E(t)`. -/
theorem completed_order_le_degree {E L : Type*} [Field E] [Finite E] [Field L]
    [Algebra (Polynomial E) L] [Algebra (FractionRing (Polynomial E)) L]
    [IsScalarTower (Polynomial E) (FractionRing (Polynomial E)) L]
    [FiniteDimensional (FractionRing (Polynomial E)) L]
    (V : ValuationSubring L) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime]
    [CharP V p] [CharP (IsLocalRing.ResidueField V) p] [Finite (IsLocalRing.ResidueField V)]
    (s : V) (hs : Irreducible s)
    (ht : algebraMap (Polynomial E) L Polynomial.X ∈ V.nonunits) :
    let τ := Residue.branchLaurentExpansion p s hs L (algebraMap (Polynomial E) L Polynomial.X)
    0 < τ.order ∧ τ.order ≤ Module.finrank (FractionRing (Polynomial E)) L := by
  let F := FractionRing (Polynomial E)
  let t := algebraMap (Polynomial E) L Polynomial.X
  let f := Residue.branchLaurentExpansion p s hs L
  let τ := f t
  let v : V := ⟨t, V.nonunits_subset ht⟩
  have hv : v ≠ 0 := by
    intro h
    have eq : t = 0 := congrArg Subtype.val h
    change algebraMap (Polynomial E) L Polynomial.X = 0 at eq
    rw [IsScalarTower.algebraMap_apply (Polynomial E) F L] at eq
    exact Polynomial.X_ne_zero (IsFractionRing.injective (Polynomial E) F
      (((algebraMap F L).injective (eq.trans (map_zero _).symm)).trans (map_zero _).symm))
  have hτ : 0 < τ.order := positive_order_at_zero p s hs v hv
    ((IsLocalRing.residue_eq_zero_iff v).mpr (V.coe_mem_nonunits_iff.mp ht))
  let φ := (f.comp (algebraMap (Polynomial E) L)).comp Polynomial.C
  have ev : f.comp (algebraMap (Polynomial E) L) = Polynomial.eval₂RingHom φ τ :=
    Polynomial.ringHom_ext (fun a => (Polynomial.eval₂_C φ τ).symm) (Polynomial.eval₂_X φ τ).symm
  have hf (q : Polynomial E) : (f.comp (algebraMap F L)) (algebraMap _ _ q) = q.eval₂ φ τ := by
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply (Polynomial E) F L]
    exact RingHom.congr_fun ev q
  have hbase (a : F) (ha : a ≠ 0) : (τ.order.toNat : ℤ) ∣ (f (algebraMap F L a)).order := by
    rw [Int.toNat_of_nonneg hτ.le]
    exact parameter_order_dvd_rational_order φ τ hτ _ hf a ha
  have hdeg := ramification_le_finrank f τ.order.toNat hbase (algebraMap V L s)
    (normalized_uniformizer_order p s hs)
  refine ⟨hτ, ?_⟩
  change τ.order ≤ (Module.finrank F L : ℤ)
  rw [← Int.toNat_of_nonneg hτ.le]
  exact_mod_cast hdeg

end Branch

end BorderVNP
end Computability
end OAI
