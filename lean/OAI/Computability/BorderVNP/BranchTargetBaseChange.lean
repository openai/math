import OAI.Computability.BorderVNP.BranchRelationsBaseChange
import OAI.Computability.BorderVNP.BranchTarget

/-! # Applying generic-target avoidance to the deformation component

A point of the graph over the original constants satisfies the extended graph relations
over the parameter field. This lets the single chosen constant target enforce chart
regularity and Jacobian nonsingularity on the actual generic deformation fiber.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

variable {I K T L : Type*} [Field K] [Field T] [Field L] [Algebra K T] [Algebra K L]
  [Algebra T L] [IsScalarTower K T L] {m : ℕ}

private noncomputable def paramHomogeneous (j : Option (Fin m)) : MvPolynomial (Fin m) K :=
  j.elim 1 X

private noncomputable def graphNums (Y : I → MvPolynomial (Fin m) K) (k : Option (Fin m)) :
    Option (Fin m) ⊕ I → MvPolynomial (Fin m) K :=
  Sum.elim paramHomogeneous (fun i => Y i * paramHomogeneous k)

private theorem generic_graph_eq (Y : I → MvPolynomial (Fin m) K) (k : Option (Fin m))
    (p : MvPolynomial (Option (Fin m) ⊕ I) K) :
    graphChartMap Y k p = aeval (fun i => algebraMap _ (ParameterField (Fin m) K) (graphNums Y k i) /
      algebraMap _ _ (paramHomogeneous (K := K) k)) p := by
  let inc := algebraMap (MvPolynomial (Fin m) K) (ParameterField (Fin m) K)
  have eq (j : Option (Fin m)) : inc (paramHomogeneous j) = homogeneousParameters (Fin m) K j := by
    cases j <;> simp [paramHomogeneous, homogeneousParameters, inc]
  have hn : inc (paramHomogeneous k) ≠ 0 := by
    apply (map_ne_zero_iff inc (IsFractionRing.injective _ _)).mpr
    cases k <;> simp [paramHomogeneous]
  rw [← graphChartAlgHom_toRingHom]
  change aeval (graphValues Y k) p = _
  congr 2
  funext j
  cases j with
  | inl j => exact (congrArg₂ (· / ·) (eq j) (eq k)).symm
  | inr i =>
    change inc (eval₂Hom C Y (X i)) = inc (Y i * paramHomogeneous k) / inc (paramHomogeneous k)
    rw [eval₂Hom_X', map_mul, mul_div_cancel_right₀ _ hn]

/-- A point over any common extension satisfying the base graph equations satisfies
the graph equations after extension of constants. -/
theorem graphChart_kernel_baseChange [Infinite K] (Y : I → MvPolynomial (Fin m) K)
    (k : Option (Fin m)) (z : Option (Fin m) ⊕ I → L)
    (hz : RingHom.ker (graphChartMap Y k) ≤ RingHom.ker (aeval (R := K) z).toRingHom) :
    RingHom.ker (graphChartMap (fun i => map (algebraMap K T) (Y i)) k) ≤
      RingHom.ker (aeval (R := T) z).toRingHom := by
  intro p hp
  let inc := algebraMap K T
  have hd (j : Option (Fin m)) : map inc (paramHomogeneous j) = paramHomogeneous j := by
    cases j <;> simp [paramHomogeneous]
  have hn (j) : graphNums (fun i => map inc (Y i)) k j = map inc (graphNums Y k j) := by
    cases j <;> simp [graphNums, hd]
  refine rational_kernel_baseChange (paramHomogeneous k) (graphNums Y k)
    (by cases k <;> simp [paramHomogeneous]) z ?_ p ?_
  · intro q hq
    apply hz
    change graphChartMap Y k q = 0
    rwa [generic_graph_eq]
  · change graphChartMap (fun i => map inc (Y i)) k p = 0 at hp
    rw [generic_graph_eq] at hp
    simp_rw [hn] at hp
    rw [hd]
    exact hp

/-- Good target values force both chart regularity and generic Jacobian nonsingularity
on points of the original constant-field graph. -/
theorem good_displacement_on_base_graph [Infinite K] (Y : I → MvPolynomial (Fin m) K)
    (k : Option (Fin m)) (t : T) (den : MvPolynomial (Fin m) T)
    (num : Fin m → MvPolynomial (Fin m) T) (ψ : Fin m → MvPolynomial (Option (Fin m) ⊕ I) T)
    (f : MvPolynomial (Fin m) T) (q : MvPolynomial (Option (Fin m) ⊕ I) T)
    (he : graphChartMap (fun i => map (algebraMap K T) (Y i)) k
      (aeval ψ f - chartException k t den num * q) = 0)
    (z : Option (Fin m) ⊕ I → L)
    (hz : RingHom.ker (graphChartMap Y k) ≤ RingHom.ker (aeval (R := K) z).toRingHom)
    (v : Fin m → T) (hv : eval v f ≠ 0) (hψ : ∀ i, aeval z (ψ i) = algebraMap T L (v i)) :
    z (.inl none) ≠ 0 ∧ aeval (z ∘ Sum.inl ∘ chartIndex k) (jacobianNumerator t den num).det ≠ 0 := by
  apply good_displacement_regular _ k t den num ψ f q he z (graphChart_kernel_baseChange Y k z hz)
  rw [funext hψ]
  have eq (p : MvPolynomial (Fin m) T) :
      aeval (fun i => algebraMap T L (v i)) p = algebraMap T L (eval v p) := by
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  rw [eq]
  exact (map_ne_zero_iff _ (algebraMap T L).injective).mpr hv

end Branch

end BorderVNP
end Computability
end OAI
