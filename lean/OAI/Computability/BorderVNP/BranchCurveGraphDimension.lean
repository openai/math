import OAI.Computability.BorderVNP.BranchCurveAffineDimension
import OAI.Computability.BorderVNP.BranchGraph
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# The dimension of the projective parameter charts

The closed graph chart has the same rational function field as the original
parameter space. Dividing each homogeneous ratio by the zeroth ratio recovers
the original independent variables. Noether normalization then determines the
dimension of the graph chart and the height at each point of its deformation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

/-- The graph chart parametrization over its scalar field. -/
noncomputable def graphChartAlgHom {σ ι K : Type*} [Field K] (Y : ι → MvPolynomial σ K)
    (k : Option σ) : MvPolynomial (Option σ ⊕ ι) K →ₐ[K] ParameterField σ K :=
  aeval (Sum.elim (fun j => homogeneousParameters σ K j / homogeneousParameters σ K k)
    (fun i => genericTable Y (X i)))

/-- The coordinate algebra map agrees with the chart equations used for the graph fiber. -/
theorem graphChartAlgHom_toRingHom {σ ι K : Type*} [Field K] (Y : ι → MvPolynomial σ K)
    (k : Option σ) : (graphChartAlgHom Y k).toRingHom = graphChartMap Y k := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change aeval _ (C a) = eval₂Hom _ _ (C a)
    rw [aeval_C, eval₂Hom_C, RingHom.comp_apply]
    change algebraMap K (ParameterField σ K) a = algebraMap _ _ (eval₂Hom C Y (C a))
    rw [eval₂Hom_C, IsScalarTower.algebraMap_apply K (MvPolynomial σ K) (ParameterField σ K)]
    rfl
  · intro i
    change aeval _ (X i) = eval₂Hom _ _ (X i)
    rw [aeval_X, eval₂Hom_X']

/-- The rational function field of the graph chart is the full parameter field. -/
theorem chart_fraction_field {σ ι K : Type*} [Field K] (Y : ι → MvPolynomial σ K)
    (k : Option σ) (hk : homogeneousParameters σ K k ≠ 0) :
    IsFractionRing (graphChartAlgHom Y k).range (ParameterField σ K) := by
  let S := (graphChartAlgHom Y k).range
  let T := IntermediateField.adjoin K (S : Set (ParameterField σ K))
  let u := homogeneousParameters σ K
  have hratio (j : Option σ) : u j / u k ∈ T :=
    IntermediateField.subset_adjoin K _ ⟨X (.inl j), aeval_X _ _⟩
  have hX (i : σ) : algebraMap (MvPolynomial σ K) (ParameterField σ K) (X i) ∈ T := by
    have h := T.div_mem (hratio (some i)) (hratio none)
    change u (some i) / u k / (1 / u k) ∈ T at h
    rw [div_div_div_cancel_right₀ hk, div_one] at h
    exact h
  have hpoly (p : MvPolynomial σ K) : algebraMap _ (ParameterField σ K) p ∈ T := by
    induction p using MvPolynomial.induction_on with
    | C a => exact T.algebraMap_mem a
    | add p q hp hq => simpa only [map_add] using T.add_mem hp hq
    | mul_X p i hp => simpa only [map_mul] using T.mul_mem hp (hX i)
  apply IsFractionRing.of_field
  intro z
  obtain ⟨p, q, _, he⟩ := IsFractionRing.div_surjective (MvPolynomial σ K) z
  have h : z ∈ T := he ▸ T.div_mem (hpoly p) (hpoly q)
  obtain ⟨x, hx, y, hy, eq⟩ := IntermediateField.mem_adjoin_iff_div.mp h
  rw [Algebra.adjoin_eq] at hx hy
  exact ⟨⟨x, hx⟩, ⟨y, hy⟩, eq⟩

/-- Each graph chart on a nonzero homogeneous parameter has dimension exactly
the number of independent parameters, regardless of the output dimension. -/
theorem chart_dimension {σ ι K : Type*} [Field K] [Finite σ] [Finite ι]
    (Y : ι → MvPolynomial σ K) (k : Option σ) (hk : homogeneousParameters σ K k ≠ 0) :
    ringKrullDim (graphChartAlgHom Y k).range = Nat.card σ := by
  classical
  let S := (graphChartAlgHom Y k).range
  have : Algebra.FiniteType K S := .of_surjective (graphChartAlgHom Y k).rangeRestrict
    (graphChartAlgHom Y k).rangeRestrict_surjective
  obtain ⟨n, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K S
  let R := MvPolynomial (Fin n) K
  let : Algebra R S := g.toRingHom.toAlgebra
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Algebra.IsIntegral R S := ⟨hint⟩
  have : IsScalarTower K R S := IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  let L := ParameterField σ K
  have : IsFractionRing S L := chart_fraction_field Y k hk
  have : Algebra.IsAlgebraic S L := IsLocalization.isAlgebraic L (nonZeroDivisors S)
  have : Algebra.IsAlgebraic (MvPolynomial σ K) L :=
    IsLocalization.isAlgebraic L (nonZeroDivisors (MvPolynomial σ K))
  let := Fintype.ofFinite σ
  have hA : IsTranscendenceBasis K (algebraMap R S ∘ X) :=
    (IsTranscendenceBasis.mvPolynomial (Fin n) K).algebraMap_comp
  have hB : IsTranscendenceBasis K (algebraMap S L ∘ algebraMap R S ∘ X) := hA.algebraMap_comp
  have hC : IsTranscendenceBasis K (algebraMap (MvPolynomial σ K) L ∘ X) :=
    (IsTranscendenceBasis.mvPolynomial σ K).algebraMap_comp
  have hcard := hB.lift_cardinalMk_eq hC
  have he : n = Nat.card σ := by simpa using hcard
  obtain ⟨m, hm, _⟩ := (⊥ : Ideal S).exists_le_maximal bot_ne_top
  exact (dimension_of_normalization m n g hinj hint).2.trans (congrArg _ he)

/-- The dimension requirement in the local height argument for (9.1) holds at
every closed point of the graph chart times the parameter line. -/
theorem chart_deformation_height {σ ι K : Type*} [Field K] [Finite σ] [Finite ι]
    (Y : ι → MvPolynomial σ K) (k : Option σ) (hk : homogeneousParameters σ K k ≠ 0)
    (m : Ideal (Polynomial (graphChartAlgHom Y k).range)) [m.IsMaximal] :
    Ideal.height (R := Polynomial (graphChartAlgHom Y k).range) m = (Nat.card σ : ℕ∞) + 1 := by
  have : Algebra.FiniteType K (graphChartAlgHom Y k).range :=
    .of_surjective (graphChartAlgHom Y k).rangeRestrict (graphChartAlgHom Y k).rangeRestrict_surjective
  have : IsNoetherianRing (graphChartAlgHom Y k).range := Algebra.FiniteType.isNoetherianRing K _
  have : Algebra.FiniteType K (Polynomial (graphChartAlgHom Y k).range) :=
    Algebra.FiniteType.trans (S := (graphChartAlgHom Y k).range) inferInstance inferInstance
  have h := affineDomain_point_height (K := K) (A := Polynomial (graphChartAlgHom Y k).range) m
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, chart_dimension Y k hk] at h
  exact_mod_cast h

/-- Coordinate ring of a prime component of an affine scheme. -/
abbrev ComponentRing {A : Type*} [CommRing A] (P : Ideal A) := A ⧸ P

/-- The deformed slices have a horizontal affine curve through the retained
isolated point on the actual graph chart. -/
theorem exists_chart_curve {σ ι K : Type*} [Field K] [Finite σ] [Finite ι]
    (Y : ι → MvPolynomial σ K) (k : Option σ) (hk : homogeneousParameters σ K k ≠ 0)
    (eqns : Finset (Polynomial (graphChartAlgHom Y k).range)) (count : eqns.card ≤ Nat.card σ)
    (m : Ideal (Polynomial (graphChartAlgHom Y k).range)) [m.IsMaximal]
    (isolated : m ∈ (Ideal.span (eqns : Set _) ⊔ Ideal.span {Polynomial.X}).minimalPrimes) :
    ∃ (P : Ideal (Polynomial (graphChartAlgHom Y k).range)),
      P ∈ (Ideal.span (eqns : Set _)).minimalPrimes ∧ P < m ∧
      ringKrullDim (ComponentRing (A := Polynomial (graphChartAlgHom Y k).range) P) = 1 ∧
      Function.Injective (Polynomial.aeval (R := K) (Ideal.Quotient.mk (R := Polynomial (graphChartAlgHom Y k).range) P Polynomial.X)) := by
  have : Algebra.FiniteType K (graphChartAlgHom Y k).range := .of_surjective
    (graphChartAlgHom Y k).rangeRestrict (graphChartAlgHom Y k).rangeRestrict_surjective
  have : Algebra.FiniteType K (Polynomial (graphChartAlgHom Y k).range) :=
    Algebra.FiniteType.trans (S := (graphChartAlgHom Y k).range) inferInstance inferInstance
  apply exists_affine_curve (K := K) (A := Polynomial (graphChartAlgHom Y k).range)
    eqns Polynomial.X m isolated
  rw [chart_deformation_height Y k hk]
  exact_mod_cast (Nat.lt_succ_of_le count)

end Branch

end BorderVNP
end Computability
end OAI
