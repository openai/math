import OAI.Computability.BorderVNP.BranchTargetBaseChange
import OAI.Computability.BorderVNP.BranchAffineJacobian

/-! # A good constant target for the cleared affine equations

Clear the affine displacement determinant in graph coordinates using
`xⱼ = z_(some j) / z_none`. Multiplying by `z_none` excludes the parameter boundary as
well. A single short constant target therefore gives the nonsingular Jacobian of the
actual affine rows on each generic deformation component through a retained point.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial VPVNP.RadicalCertificate

variable {I K T L : Type*} [Field K] [Field T] [Field L] [Algebra K T] [Algebra K L]
  [Algebra T L] [IsScalarTower K T L] {m d D : ℕ}

/-- Polynomial on the graph obtained by clearing the affine determinant to degree `s`
and multiplying by the boundary coordinate. -/
noncomputable def affineChartException (k : Option (Fin m)) (t : T) (A : Fin m → MvPolynomial (Fin m) T)
    (s : ℕ) : MvPolynomial (Option (Fin m) ⊕ I) T :=
  X (.inl none) * clearedSubstitution (X (.inl none)) (fun i => X (.inl (some i))) s
    (affineDisplacementJacobian k t A)

/-- On any finite-parameter point of the graph the affine determinant is recovered
from the exceptional polynomial by a nonzero power of the boundary coordinate. -/
theorem aeval_affineChartException (k : Option (Fin m)) (t : T) (A : Fin m → MvPolynomial (Fin m) T)
    (s : ℕ) (hD : (affineDisplacementJacobian k t A).totalDegree ≤ s)
    (z : Option (Fin m) ⊕ I → L) (x : Fin m → L) (hx : ∀ i, x i * z (.inl none) = z (.inl (some i))) :
    aeval z (affineChartException k t A s) =
      z (.inl none) * (aeval x (affineDisplacementJacobian k t A) * z (.inl none)^s) := by
  rw [affineChartException, map_mul, aeval_X, eval_clearedSubstitution z x _ _
    (fun i => by simpa only [aeval_X] using hx i) _ hD, aeval_X]

private theorem graph_affine_exception (Y : I → MvPolynomial (Fin m) T) (k : Option (Fin m))
    (t : T) (A : Fin m → MvPolynomial (Fin m) T) (s : ℕ)
    (hD : (affineDisplacementJacobian k t A).totalDegree ≤ s) (hne : affineDisplacementJacobian k t A ≠ 0) :
    graphChartMap Y k (affineChartException k t A s) ≠ 0 := by
  let z := graphValues Y k
  let x := affineParameter m T
  let u := homogeneousParameters (Fin m) T
  have hu : u k ≠ 0 := by
    cases k with
    | none => exact one_ne_zero
    | some i => exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (X_ne_zero i)
  have hfront : z (.inl none) ≠ 0 := div_ne_zero one_ne_zero hu
  have hx (i) : x i * z (.inl none) = z (.inl (some i)) := by
    change x i * (1 / u k) = x i / u k
    rw [one_div, div_eq_mul_inv]
  rw [← graphChartAlgHom_toRingHom]
  change aeval z _ ≠ 0
  rw [aeval_affineChartException _ _ _ _ hD z x hx]
  change _ * (aeval (affineParameter m T) _ * _) ≠ 0
  rw [eval_affineParameter]
  exact mul_ne_zero hfront (mul_ne_zero
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hne) (pow_ne_zero _ hfront))

/-- A single bounded finite constant extension and target avoiding the boundary and
the singular locus of the original affine rows. The underlying row polynomial family
is obtained by clearing degree-one slices on the chart. -/
theorem exists_good_affine_target (E₀ : Type*) [Field E₀] [Fintype E₀] [Algebra E₀ K] [IsAlgClosed K]
    [Infinite T] [Algebra (Polynomial K) T] [IsScalarTower K (Polynomial K) T]
    [IsFractionRing (Polynomial K) T] (Y : I → MvPolynomial (Fin m) T) (k : Option (Fin m))
    (hY : ∀ i, (Y i).totalDegree ≤ d) (A : Fin m → MvPolynomial (Fin m) K)
    (hD : 1 ≤ D) (hA : ∀ i, (A i).totalDegree ≤ D)
    (ψ : Fin m → MvPolynomial (Option (Fin m) ⊕ I) T) (hψ : ∀ i, (ψ i).totalDegree ≤ 1) :
    let t := algebraMap (Polynomial K) T Polynomial.X
    let exc : MvPolynomial (Option (Fin m) ⊕ I) T :=
      affineChartException k t (fun i => map (algebraMap K T) (A i)) (m*(2*D))
    ∃ E : IntermediateField E₀ K, Finite E ∧ Nat.card E ≤ Fintype.card E₀ * max (displacementDegree m d D) 1 ∧
      ∃ (v : Fin m → E) (f : MvPolynomial (Fin m) T), eval (fun i => algebraMap K T (v i : K)) f ≠ 0 ∧
        ∃ q, graphChartMap Y k (aeval ψ f - exc*q) = 0 := by
  classical
  let t := algebraMap (Polynomial K) T Polynomial.X
  let A' (i) := map (algebraMap K T) (A i)
  let s := m*(2*D)
  let exc : MvPolynomial (Option (Fin m) ⊕ I) T := affineChartException k t A' s
  have hD' : (affineDisplacementJacobian k t A').totalDegree ≤ s :=
    affineDisplacementJacobian_degree k t A' hD (fun i => by
      simpa only [A', totalDegree, support_map_of_injective _ (algebraMap K T).injective] using hA i)
  have hn : graphChartMap Y k exc ≠ 0 :=
    graph_affine_exception Y k t A' s hD' (affineDisplacementJacobian_generic k A)
  have hdeg : exc.totalDegree ≤ s+1 := by
    apply (totalDegree_mul ..).trans
    rw [totalDegree_X, Nat.add_comm]
    apply Nat.add_le_add_right
    simpa only [Nat.mul_one] using clearedSubstitution_degree (K := T) (σ := Option (Fin m) ⊕ I) (X (.inl none)) (fun i => X (.inl (some i)))
      (d := 1) (e := s) (by simp) (fun _ => by simp) (affineDisplacementJacobian k t A') hD'
  obtain ⟨f, hf, hfd, q, hq⟩ := graphChart_bad_locus Y k hY exc ψ hn hdeg
    (fun i => (hψ i).trans (by omega))
  obtain ⟨E, hE, hlo, hhi⟩ := exists_gridExtension E₀ K (displacementDegree m d D)
  let := Fintype.ofFinite E
  let inc := (algebraMap K T).comp E.subtype
  have hfdeg : f.totalDegree ≤ displacementDegree m d D := hfd
  obtain ⟨v, hv⟩ := exists_constants_avoiding inc (fun _ : Fin 1 => f) (fun _ => hf)
    (by simpa [← Nat.card_eq_fintype_card] using hfdeg.trans_lt hlo)
  exact ⟨E, hE, hhi, v, f, hv 0, q, hq⟩

/-- At a root on the good constant fiber the square system in the original affine
parameters has nonzero Jacobian. The chart point only needs the original field equations. -/
theorem good_affine_target_nonsingular [Infinite K] (Y : I → MvPolynomial (Fin m) K)
    (k : Option (Fin m)) (t : T) (A : Fin m → MvPolynomial (Fin m) T) (s : ℕ)
    (hD : (affineDisplacementJacobian k t A).totalDegree ≤ s)
    (ψ : Fin m → MvPolynomial (Option (Fin m) ⊕ I) T)
    (f : MvPolynomial (Fin m) T) (q : MvPolynomial (Option (Fin m) ⊕ I) T)
    (he : graphChartMap (fun i => map (algebraMap K T) (Y i)) k
      (aeval ψ f - affineChartException k t A s * q) = 0)
    (z : Option (Fin m) ⊕ I → L)
    (hz : RingHom.ker (graphChartMap Y k) ≤ RingHom.ker (aeval (R := K) z).toRingHom)
    (v : Fin m → T) (hv : eval v f ≠ 0) (hψ : ∀ i, aeval z (ψ i) = algebraMap T L (v i)) :
    z (.inl none) ≠ 0 ∧
      let x := fun i => z (.inl (some i)) / z (.inl none)
      (∀ i, aeval x (affineRow k t A v i) = 0) →
      (Matrix.of fun i j => aeval x (pderiv j (affineRow k t A v i))).det ≠ 0 := by
  have he' : aeval z (aeval ψ f - affineChartException k t A s * q) = 0 :=
    graphChart_kernel_baseChange Y k z hz he
  rw [map_sub, sub_eq_zero, map_mul, ← AlgHom.comp_apply (aeval z) (aeval ψ), comp_aeval, funext hψ] at he'
  have hf : aeval (fun i => algebraMap T L (v i)) f ≠ 0 := by
    change eval₂ (algebraMap T L) ((algebraMap T L) ∘ v) f ≠ 0
    rw [← eval_map, ← map_eval]
    exact (map_ne_zero_iff _ (algebraMap T L).injective).mpr hv
  rw [he', mul_ne_zero_iff] at hf
  have hn := hf.1
  rw [affineChartException, map_mul, aeval_X, mul_ne_zero_iff] at hn
  let x (i) := z (.inl (some i)) / z (.inl none)
  have hx (i) : x i * z (.inl none) = z (.inl (some i)) := div_mul_cancel₀ _ hn.1
  have h := hf.1
  rw [aeval_affineChartException k t A s hD z x hx, mul_ne_zero_iff, mul_ne_zero_iff] at h
  exact ⟨hn.1, fun hroot => nonsingular_affineRow k t A v x hroot h.2.1⟩

end Branch

end BorderVNP
end Computability
end OAI
