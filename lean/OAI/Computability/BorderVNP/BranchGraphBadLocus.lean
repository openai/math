import OAI.Computability.BorderVNP.BranchRationalSubstitution
import OAI.Computability.BorderVNP.BranchCurveGraphDimension

/-! # Exceptional hypersurfaces for the projective graph chart

Use the manuscript's chart of the graph itself as the source. The defining polynomial
identity remains valid on all points of its closed graph, including the parameter
boundary. The input to the final avoidance step is an explicit bound for the exceptional
function and the chosen map on that graph.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial VPVNP.RadicalCertificate

variable {I K : Type*} [Field K] {m d e : ℕ}

/-- Coordinate values in the generic field of a standard projective chart. -/
noncomputable def graphValues (Y : I → MvPolynomial (Fin m) K) (k : Option (Fin m)) :
    Option (Fin m) ⊕ I → ParameterField (Fin m) K :=
  Sum.elim (fun j => homogeneousParameters (Fin m) K j / homogeneousParameters (Fin m) K k)
    (fun i => genericTable Y (X i))

/-- Generic affine input coordinates of the polynomial table. -/
noncomputable def affineParameter (m : ℕ) (K : Type*) [Field K] (j : Fin m) :
    ParameterField (Fin m) K := algebraMap _ _ (X j : MvPolynomial (Fin m) K)

/-- Evaluation at the generic parameters is the fraction-field inclusion. -/
theorem eval_affineParameter (p : MvPolynomial (Fin m) K) :
    aeval (affineParameter m K) p = algebraMap _ (ParameterField (Fin m) K) p := by
  let inc := IsScalarTower.toAlgHom K (MvPolynomial (Fin m) K) (ParameterField (Fin m) K)
  have h : aeval (affineParameter m K) = inc := by ext j; simp [inc, affineParameter]
  exact AlgHom.congr_fun h p

/-- In a graph chart all ratios and outputs have one denominator of degree at most one
and numerators of degree at most one more than the table degree. -/
theorem graphValues_rational (Y : I → MvPolynomial (Fin m) K) (k : Option (Fin m))
    (hY : ∀ i, (Y i).totalDegree ≤ d) :
    ∃ (den : MvPolynomial (Fin m) K) (num : Option (Fin m) ⊕ I → MvPolynomial (Fin m) K),
      aeval (affineParameter m K) den ≠ 0 ∧ den.totalDegree ≤ 1 ∧
      (∀ j, (num j).totalDegree ≤ d+1) ∧ ∀ j,
      graphValues Y k j * aeval (affineParameter m K) den = aeval (affineParameter m K) (num j) := by
  let u : Option (Fin m) → MvPolynomial (Fin m) K := fun j => j.elim 1 X
  let inc := algebraMap (MvPolynomial (Fin m) K) (ParameterField (Fin m) K)
  have hu (j) : inc (u j) = homogeneousParameters (Fin m) K j := by
    cases j <;> simp [inc, u, homogeneousParameters]
  have hn (j) : inc (u j) ≠ 0 := by
    apply (map_ne_zero_iff inc (IsFractionRing.injective _ _)).mpr
    cases j <;> simp [u]
  have hd (j) : (u j).totalDegree ≤ 1 := by cases j <;> simp [u]
  refine ⟨u k, Sum.elim u (fun i => Y i * u k), by rw [eval_affineParameter]; exact hn k, hd k, ?_, ?_⟩
  · rintro (j | i)
    · exact (hd j).trans (by omega)
    · exact (totalDegree_mul ..).trans (Nat.add_le_add (hY i) (hd k))
  · rintro (j | i)
    · simp only [eval_affineParameter, Sum.elim_inl, graphValues]
      change _ / _ * inc (u k) = inc (u j)
      rw [← hu, ← hu, div_mul_cancel₀ _ (hn k)]
    · simp only [eval_affineParameter, Sum.elim_inr, graphValues, genericTable, RingHom.comp_apply,
        eval₂Hom_X', map_mul]

/-- An explicit bounded target equation avoids the image of the zero locus of `δ`
on the entire graph chart. It suffices to check `δ` at the generic chart parameters. -/
theorem graphChart_bad_locus [Infinite K] (Y : I → MvPolynomial (Fin m) K) (k : Option (Fin m))
    (hY : ∀ i, (Y i).totalDegree ≤ d) (δ : MvPolynomial (Option (Fin m) ⊕ I) K)
    (ψ : Fin m → MvPolynomial (Option (Fin m) ⊕ I) K) (hδ : graphChartMap Y k δ ≠ 0)
    (hδd : δ.totalDegree ≤ e) (hψd : ∀ j, (ψ j).totalDegree ≤ e) :
    ∃ f : MvPolynomial (Fin m) K, f ≠ 0 ∧ f.totalDegree ≤ perronSimplexBound (m+1) (e*(d+1)+1) ∧
      ∃ q : MvPolynomial (Option (Fin m) ⊕ I) K, graphChartMap Y k (aeval ψ f - δ*q) = 0 := by
  have eq (p : MvPolynomial (Option (Fin m) ⊕ I) K) :
      aeval (graphValues Y k) p = graphChartMap Y k p := by rw [← graphChartAlgHom_toRingHom]; rfl
  obtain ⟨den, num, hd, hdd, hn, hg⟩ := graphValues_rational Y k hY
  obtain ⟨f, hf, hfd, q, he⟩ := rational_chart_bad_locus (affineParameter m K) (graphValues Y k)
    den num hd (hdd.trans (by omega)) hn hg δ ψ (eq δ ▸ hδ) hδd hψd
  exact ⟨f, hf, hfd, q, (eq _) ▸ he⟩

end Branch

end BorderVNP
end Computability
end OAI
