import OAI.Computability.BorderVNP.BranchChartIndependent
import OAI.Computability.BorderVNP.BranchGrid
import OAI.Computability.BorderVNP.BranchGridExtension
import OAI.Computability.BorderVNP.BranchJacobianGeneric

/-! # Choosing the constant displacement in Proposition 9.2

A single target over a finite extension avoids both the parameter boundary and the
zero of the deformed Jacobian. The construction works over the rational function
field in `t`, but the coordinates of the displacement are constants. The displayed
bound controls the cardinality of their finite advice field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial VPVNP.RadicalCertificate

variable {K T I : Type*} [Field K] [Field T] [Algebra K T] {m d D : ℕ}

/-- Total degree of the target equation used to choose the finite grid. -/
def displacementDegree (h tableDegree rowDegree : ℕ) : ℕ :=
  perronSimplexBound (h+1) ((h*(2*rowDegree)+1)*(tableDegree+1)+1)

/-- The product of the boundary coordinate and the cleared Jacobian determinant
on the specified chart. -/
noncomputable def chartException (k : Option (Fin m)) (t : T)
    (den : MvPolynomial (Fin m) T) (num : Fin m → MvPolynomial (Fin m) T) :
    MvPolynomial (Option (Fin m) ⊕ I) T :=
  X (.inl none) * rename (Sum.inl ∘ chartIndex k) (jacobianNumerator t den num).det

/-- One polynomial identity excludes the boundary and singular locus on all generic
fibers over targets where its left side is nonzero. -/
theorem graph_deformation_exception [Infinite K] [Infinite T] [Algebra (Polynomial K) T]
    [IsScalarTower K (Polynomial K) T] [IsFractionRing (Polynomial K) T]
    (Y : I → MvPolynomial (Fin m) T) (k : Option (Fin m)) (hd : ∀ i, (Y i).totalDegree ≤ d)
    (den : MvPolynomial (Fin m) K) (num : Fin m → MvPolynomial (Fin m) K) (hne : den ≠ 0)
    (hden : den.totalDegree ≤ D) (hnum : ∀ j, (num j).totalDegree ≤ D)
    (ψ : Fin m → MvPolynomial (Option (Fin m) ⊕ I) T) (hψ : ∀ i, (ψ i).totalDegree ≤ 1) :
    let t := algebraMap (Polynomial K) T Polynomial.X
    let exc : MvPolynomial (Option (Fin m) ⊕ I) T :=
      chartException k t (map (algebraMap K T) den) (fun i => map (algebraMap K T) (num i))
    ∃ f : MvPolynomial (Fin m) T, f ≠ 0 ∧ f.totalDegree ≤ displacementDegree m d D ∧
      ∃ q, graphChartMap Y k (aeval ψ f - exc*q) = 0 := by
  let inc := algebraMap K T
  let t := algebraMap (Polynomial K) T Polynomial.X
  let J := (jacobianNumerator t (map inc den) (fun i => map inc (num i))).det
  have hJ : J ≠ 0 := generic_jacobianNumerator_ne_zero den num hne
  have hN : graphChartMap Y k (X (.inl none)) ≠ 0 := by
    change eval₂Hom _ _ (X _) ≠ 0
    rw [eval₂Hom_X']
    change 1 / homogeneousParameters (Fin m) T k ≠ 0
    cases k with
    | none => simp [homogeneousParameters]
    | some i =>
      apply div_ne_zero one_ne_zero
      exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (X_ne_zero i)
  let exc : MvPolynomial (Option (Fin m) ⊕ I) T := X (.inl none) * rename (Sum.inl ∘ chartIndex k) J
  have he : graphChartMap Y k exc ≠ 0 := by
    change graphChartMap Y k (_ * _) ≠ 0
    rw [map_mul]
    exact mul_ne_zero hN (graphChart_rename_ne_zero Y k J hJ)
  have hm (p : MvPolynomial (Fin m) K) : (map inc p).totalDegree = p.totalDegree := by
    simp only [totalDegree, support_map_of_injective p inc.injective]
  have hJD : J.totalDegree ≤ m*(2*D) := by
    simpa using jacobianNumerator_det_degree t (map inc den) (fun i => map inc (num i))
      ((hm den) ▸ hden) (fun i => (hm (num i)) ▸ hnum i)
  have hED : exc.totalDegree ≤ m*(2*D)+1 := by
    apply (totalDegree_mul ..).trans
    rw [totalDegree_X, Nat.add_comm]
    exact Nat.add_le_add_right ((totalDegree_rename_le ..).trans hJD) _
  exact graphChart_bad_locus Y k hd exc ψ he hED (fun i => (hψ i).trans (by omega))

/-- Choose a finite extension and a single constant target for the generic deformation.
Its field cardinality is at most the ground cardinality times the target degree bound. -/
theorem exists_good_displacement (E₀ : Type*) [Field E₀] [Fintype E₀] [Algebra E₀ K]
    [IsAlgClosed K] [Infinite T] [Algebra (Polynomial K) T] [IsScalarTower K (Polynomial K) T]
    [IsFractionRing (Polynomial K) T] (Y : I → MvPolynomial (Fin m) T) (k : Option (Fin m))
    (hd : ∀ i, (Y i).totalDegree ≤ d) (den : MvPolynomial (Fin m) K)
    (num : Fin m → MvPolynomial (Fin m) K) (hne : den ≠ 0) (hden : den.totalDegree ≤ D)
    (hnum : ∀ j, (num j).totalDegree ≤ D) (ψ : Fin m → MvPolynomial (Option (Fin m) ⊕ I) T)
    (hψ : ∀ i, (ψ i).totalDegree ≤ 1) :
    let t := algebraMap (Polynomial K) T Polynomial.X
    let exc : MvPolynomial (Option (Fin m) ⊕ I) T :=
      chartException k t (map (algebraMap K T) den) (fun i => map (algebraMap K T) (num i))
    ∃ E : IntermediateField E₀ K, Finite E ∧
      Nat.card E ≤ Fintype.card E₀ * max (displacementDegree m d D) 1 ∧
      ∃ (v : Fin m → E) (f : MvPolynomial (Fin m) T),
        eval (fun i => algebraMap K T (v i : K)) f ≠ 0 ∧
        ∃ q, graphChartMap Y k (aeval ψ f - exc*q) = 0 := by
  classical
  obtain ⟨f, hf, hfd, q, hq⟩ := graph_deformation_exception Y k hd den num hne hden hnum ψ hψ
  obtain ⟨E, hE, hlo, hhi⟩ := exists_gridExtension E₀ K (displacementDegree m d D)
  let := Fintype.ofFinite E
  let inc := (algebraMap K T).comp E.subtype
  obtain ⟨v, hv⟩ := exists_constants_avoiding inc (fun _ : Fin 1 => f) (fun _ => hf)
    (by simpa [← Nat.card_eq_fintype_card] using hfd.trans_lt hlo)
  exact ⟨E, hE, hhi, v, f, hv 0, q, hq⟩

/-- At a graph point above a good target both the boundary coordinate and the chart
Jacobian numerator are nonzero. This applies to points over arbitrary extensions. -/
theorem good_displacement_regular {L : Type*} [Field L] [Algebra T L]
    (Y : I → MvPolynomial (Fin m) T) (k : Option (Fin m)) (t : T)
    (den : MvPolynomial (Fin m) T) (num : Fin m → MvPolynomial (Fin m) T)
    (ψ : Fin m → MvPolynomial (Option (Fin m) ⊕ I) T)
    (f : MvPolynomial (Fin m) T) (q : MvPolynomial (Option (Fin m) ⊕ I) T)
    (he : graphChartMap Y k (aeval ψ f - chartException k t den num * q) = 0)
    (z : Option (Fin m) ⊕ I → L) (hz : RingHom.ker (graphChartMap Y k) ≤ RingHom.ker (aeval z).toRingHom)
    (hf : aeval (fun i => aeval z (ψ i)) f ≠ 0) :
    z (.inl none) ≠ 0 ∧ aeval (z ∘ Sum.inl ∘ chartIndex k) (jacobianNumerator t den num).det ≠ 0 := by
  have h : aeval z (aeval ψ f - chartException k t den num * q) = 0 := hz he
  rw [map_sub, map_mul, sub_eq_zero, ← AlgHom.comp_apply (aeval z) (aeval ψ), comp_aeval] at h
  rw [h, mul_ne_zero_iff] at hf
  simpa only [chartException, map_mul, aeval_X, aeval_rename, mul_ne_zero_iff, Function.comp_assoc]
    using hf.1

end Branch

end BorderVNP
end Computability
end OAI
