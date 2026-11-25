import OAI.Computability.BorderVNP.BranchCurveIsolated
import OAI.Computability.BorderVNP.BranchAffineRows
import OAI.Computability.BorderVNP.BranchCurveComponentField
import OAI.Computability.BorderVNP.BranchCurveModel

/-!
# The horizontal geometric branch through the prescribed output

The special-fiber point of the sliced parameter graph lifts to a function field
over the parameter line. Its finite-parameter generic point satisfies the
deformed square system with invertible Jacobian, while its discrete valuation
specializes all output coordinates simultaneously.
-/

namespace OAI
namespace Computability
namespace BorderVNP

universe u

namespace Branch

open MvPolynomial

variable {K : Type u} [Field K] {I : Type*} {h d : ℕ}

private theorem branch_on_component {A L : Type u} [CommRing A] [Field L]
    [Algebra K A] [Algebra K L] [Algebra A L] [IsScalarTower K A L] [IsFractionRing A L]
    [Algebra (Polynomial K) A] [Algebra (Polynomial K) L] [IsScalarTower (Polynomial K) A L]
    [Algebra (FractionRing (Polynomial K)) L] [IsScalarTower K (FractionRing (Polynomial K)) L]
    [IsScalarTower (Polynomial K) (FractionRing (Polynomial K)) L]
    [Infinite K] (Y : I → MvPolynomial (Fin h) K) (k : Option (Fin h))
    (hk : homogeneousParameters (Fin h) K k ≠ 0)
    (D : Fin h → MvPolynomial (Option (Fin h) ⊕ I) K) (hD : ∀ i, (D i).totalDegree ≤ 1)
    (hY : ∀ i, (Y i).totalDegree ≤ d)
    (t : FractionRing (Polynomial K)) (ht : t = algebraMap (Polynomial K) _ Polynomial.X)
    (v : Fin h → K) (f : MvPolynomial (Fin h) (FractionRing (Polynomial K)))
    (hv : eval (algebraMap K _ ∘ v) f ≠ 0)
    (q : MvPolynomial (Option (Fin h) ⊕ I) (FractionRing (Polynomial K)))
    (he : graphChartMap (fun i => map (algebraMap K (FractionRing (Polynomial K))) (Y i)) k
      (aeval (displacementMap k t D) f - affineChartException k t
        (fun i => map (algebraMap K _) (affineSlice Y k (D i))) (h*(2*(d+1))) * q) = 0)
    (π : Polynomial (ChartRing Y k) →ₐ[K] A) (hπ : Function.Surjective π)
    (hparam : π Polynomial.X = algebraMap (Polynomial K) A Polynomial.X)
    (hdeform : ∀ i, π (Polynomial.C ((graphChartAlgHom Y k).rangeRestrict (D i)) + Polynomial.X *
      Polynomial.C (chartRatio Y k (chartIndex k i) - algebraMap K _ (v i))) = 0)
    (point : A →ₐ[K] K) (c : I → K) (hzero : point (π Polynomial.X) = 0)
    (hc : ∀ i, point (π (Polynomial.C (chartOutput Y k i))) = c i) :
    Nonempty (GeometricBranch Y c (affineRow k t
      (fun i => map (algebraMap K _) (affineSlice Y k (D i))) (algebraMap K _ ∘ v))) := by
  let T := FractionRing (Polynomial K)
  let φ := (IsScalarTower.toAlgHom K A L).comp (π.comp (IsScalarTower.toAlgHom K
    (ChartRing Y k) (Polynomial (ChartRing Y k))))
  have hφ (r : ChartRing Y k) : φ r = algebraMap A L (π (Polynomial.C r)) := rfl
  have t_nonzero : t ≠ 0 := by
    rw [ht]
    intro h0
    exact Polynomial.X_ne_zero ((IsFractionRing.injective (Polynomial K) T)
      (h0.trans (map_zero _).symm))
  have hline : algebraMap A L (π Polynomial.X) = algebraMap T L t := by
    rw [hparam, ht, ← IsScalarTower.algebraMap_apply (Polynomial K) A L,
      ← IsScalarTower.algebraMap_apply (Polynomial K) T L]
  have hroot (i : Fin h) : φ ((graphChartAlgHom Y k).rangeRestrict (D i)) + algebraMap T L t *
      (φ (chartRatio Y k (chartIndex k i)) - algebraMap T L ((algebraMap K T ∘ v) i)) = 0 := by
    have eq := congrArg (algebraMap A L) (hdeform i)
    simp only [map_add, map_mul, map_zero] at eq
    rw [← hφ, ← hφ, map_sub, AlgHom.commutes, hline] at eq
    simpa only [Function.comp_apply, ← IsScalarTower.algebraMap_apply K T L] using eq
  obtain ⟨hd, hg, hJ⟩ := affine_slice_component_root Y k hk D hD hY t t_nonzero
    (algebraMap K T ∘ v) f hv q he φ hroot
  have hgen := chart_generates_component Y k hk π hπ φ hφ hd ⟨t, hline⟩
  obtain ⟨hfin, hsep⟩ := finite_separable_of_nonsingular_system _ _ hgen hg hJ
  obtain ⟨V, hdis, reg, hz, res⟩ := chart_place_realizes_outputs Y k hk π hπ hparam φ hφ hd
    point c hzero hc _ hg hJ
  refine ⟨⟨L, chartParameters Y k φ, hgen, hfin, hsep, hg, hJ, V, hdis, fun p => ?_, ?_, res⟩⟩
  · rw [← IsScalarTower.algebraMap_apply (Polynomial K) T L]
    exact reg p
  · rwa [← IsScalarTower.algebraMap_apply (Polynomial K) T L]

private theorem use_chart_component {S : Type u} [CommRing S] [Algebra K S]
    (δ : Fin h → Polynomial S) (χ : S →ₐ[K] K)
    (P : Ideal (Polynomial S)) [P.IsPrime] (hmem : ∀ i, δ i ∈ P)
    (hthrough : P ≤ RingHom.ker (Polynomial.aevalTower χ 0))
    (ha : Function.Injective (Polynomial.aeval (R := K)
      (Ideal.Quotient.mk (R := Polynomial S) P Polynomial.X)))
    {claim : Prop}
    (finish : ∀ (A L : Type u) [CommRing A] [Field L] [Algebra K A] [Algebra K L]
      [Algebra A L] [IsScalarTower K A L] [IsFractionRing A L]
      [Algebra (Polynomial K) A] [Algebra (Polynomial K) L] [IsScalarTower (Polynomial K) A L]
      [Algebra (FractionRing (Polynomial K)) L] [IsScalarTower K (FractionRing (Polynomial K)) L]
      [IsScalarTower (Polynomial K) (FractionRing (Polynomial K)) L]
      (π : Polynomial S →ₐ[K] A), Function.Surjective π →
        π Polynomial.X = algebraMap (Polynomial K) A Polynomial.X →
        (∀ i, π (δ i) = 0) → ∀ point : A →ₐ[K] K, point (π Polynomial.X) = 0 →
          (∀ r : S, point (π (Polynomial.C r)) = χ r) → claim) : claim := by
  let A := ComponentRing (A := Polynomial S) P
  let π : Polynomial S →ₐ[K] A := Ideal.Quotient.mkₐ (A := Polynomial S) K P
  let a : A := π Polynomial.X
  let := (Polynomial.aeval (R := K) a).toRingHom.toAlgebra
  let := (Decision.parameterFractionMap K a ha).toAlgebra
  obtain ⟨hline, hfrac, hbase, _, ht⟩ := component_scalar_towers K a ha
  obtain ⟨point, hzero, hs⟩ := special_point_on_component χ P hthrough
  exact finish A (FractionRing A) π (Ideal.Quotient.mkₐ_surjective K P) ht
    (fun i => Ideal.Quotient.eq_zero_iff_mem.mpr (hmem i)) point hzero hs

set_option maxHeartbeats 500000 in
/-- A finite weighted special fiber and a displacement target avoiding the
exceptional polynomial produce a discrete, finite separable branch through
the retained point with all the prescribed output residues. -/
theorem geometric_branch_of_finite_slice [IsAlgClosed K] [Finite I]
    (Y : I → MvPolynomial (Fin h) K) (k : Option (Fin h))
    (hk : homogeneousParameters (Fin h) K k ≠ 0)
    (D : Fin h → MvPolynomial (Option (Fin h) ⊕ I) K) (hD : ∀ i, (D i).totalDegree ≤ 1)
    (hY : ∀ i, (Y i).totalDegree ≤ d)
    (finite : {x ∈ zeroLocus K (RingHom.ker (graphChartMap Y k)) |
      ∀ i, eval x (D i) = 0}.Finite)
    (z : Option (Fin h) → K) (c : I → K)
    (retained : Sum.elim z c ∈ zeroLocus K (RingHom.ker (graphChartMap Y k)))
    (cuts : ∀ i, eval (Sum.elim z c) (D i) = 0)
    (v : Fin h → K) (f : MvPolynomial (Fin h) (FractionRing (Polynomial K)))
    (hv : eval (algebraMap K _ ∘ v) f ≠ 0)
    (q : MvPolynomial (Option (Fin h) ⊕ I) (FractionRing (Polynomial K))) :
    let T := FractionRing (Polynomial K)
    let t := algebraMap (Polynomial K) T Polynomial.X
    let A := fun i => map (algebraMap K T) (affineSlice Y k (D i))
    graphChartMap (fun i => map (algebraMap K T) (Y i)) k
      (aeval (displacementMap k t D) f - affineChartException k t A (h*(2*(d+1))) * q) = 0 →
    Nonempty (GeometricBranch Y c (affineRow k t A (algebraMap K T ∘ v))) := by
  classical
  intro T t _ he
  let S : Type u := ChartRing Y k
  let ρ : MvPolynomial (Option (Fin h) ⊕ I) K →ₐ[K] S := (graphChartAlgHom Y k).rangeRestrict
  let δ (i : Fin h) := Polynomial.C (ρ (D i)) + Polynomial.X *
    Polynomial.C (chartRatio Y k (chartIndex k i) - algebraMap K S (v i))
  let eqns := Finset.univ.image δ
  have eqs : (eqns : Set _) = Set.range δ := by simp [eqns]
  obtain ⟨χ, hχr, hχo⟩ := graph_point_character Y k z c retained
  have ev : χ.comp ρ = aeval (R := K) (Sum.elim z c) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, aeval_X]
    cases i with
    | inl j => exact hχr j
    | inr j => exact hχo j
  have hcut (i : Fin h) : χ (ρ (D i)) = 0 := by
    change (χ.comp ρ) (D i) = 0
    rw [ev]
    exact cuts i
  have ker : RingHom.ker ρ.toRingHom = RingHom.ker (graphChartMap Y k) :=
    (AlgHom.ker_rangeRestrict (graphChartAlgHom Y k)).trans (congrArg RingHom.ker
      (graphChartAlgHom_toRingHom Y k))
  let m := RingHom.ker (Polynomial.aevalTower χ 0)
  have : m.IsMaximal := RingHom.ker_isMaximal_of_surjective (Polynomial.aevalTower χ 0)
    fun r => ⟨algebraMap K _ r, (Polynomial.aevalTower χ 0).commutes r⟩
  have isolated : m ∈ (Ideal.span (eqns : Set _) ⊔ Ideal.span {Polynomial.X}).minimalPrimes := by
    rw [eqs]
    refine isolated_point_of_finite_fiber ρ.toRingHom (graphChartAlgHom Y k).rangeRestrict_surjective
      D δ (fun i => by simp [δ]) ?_ χ hcut
    rwa [ker]
  have count : eqns.card ≤ Nat.card (Fin h) := by
    simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using (Finset.card_image_le
      (f := δ) (s := Finset.univ))
  obtain ⟨P, hP, hPm, _, hdom⟩ := exists_chart_curve Y k hk eqns count m isolated
  have : P.IsPrime := hP.isPrime
  apply use_chart_component (S := S) δ χ P (fun i => hP.le (Ideal.subset_span
    (eqs ▸ Set.mem_range_self i))) hPm.le hdom
  intro A L _ _ _ _ _ _ _ _ _ _ _ _ _ π hπ ht eqn point hzero hs
  exact branch_on_component (A := A) (L := L) Y k hk D hD hY t rfl v f hv q he
    π hπ ht eqn point c hzero (fun i => (hs _).trans (hχo i))

end Branch

end BorderVNP
end Computability
end OAI
