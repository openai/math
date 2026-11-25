import OAI.Computability.BorderVNP.BranchGraphFiber
import OAI.Computability.BorderVNP.BranchSlice

/-!
# Weighted graph equations and their base locus

On the graph chart the slice polynomial has one coefficient for each output residual
and each short coordinate pin. Its zero polynomial therefore cuts out exactly the
retained finite fiber. This remains true in positive characteristic, because the
digit exponents are distinct.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

variable {I J K : Type*} [Field K] [Fintype J]

/-- A polynomial in the slice scalar with graph equations as its coefficients. -/
noncomputable def weightedGraph (e : J → ℕ) (f : J → MvPolynomial I K) :
    Polynomial (MvPolynomial I K) := ∑ j, Polynomial.monomial (e j) (f j)

/-- Evaluating the graph point gives the weighted sum of all equations at that point. -/
theorem eval_weightedGraph (e : J → ℕ) (f : J → MvPolynomial I K) (v : I → K) (a : K) :
    ((weightedGraph e f).map (eval v)).eval a = ∑ j, eval v (f j) * a^(e j) := by
  simp [weightedGraph, Polynomial.map_sum, Polynomial.eval_finsetSum]

/-- Each original equation is recovered from its designated coefficient. -/
theorem weightedGraph_coeff (e : J → ℕ) (he : Function.Injective e) (f : J → MvPolynomial I K)
    (j : J) : (weightedGraph e f).coeff (e j) = f j := by
  classical
  simp [weightedGraph, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, he.eq_iff]

/-- The weighted polynomial is zero precisely on the common zero locus of the residuals. -/
theorem map_weightedGraph_eq_zero_iff (e : J → ℕ) (he : Function.Injective e)
    (f : J → MvPolynomial I K) (v : I → K) :
    (weightedGraph e f).map (eval v) = 0 ↔ ∀ j, eval v (f j) = 0 := by
  constructor
  · intro hz j
    have h := congrArg (Polynomial.coeff · (e j)) hz
    simpa only [Polynomial.coeff_map, weightedGraph_coeff e he, Polynomial.coeff_zero] using h
  · intro h
    simp [weightedGraph, Polynomial.map_sum, h]

/-- Uniform degree bounds for the univariate weighting and each of its graph coefficients. -/
theorem weightedGraph_bounds (e : J → ℕ) (he : Function.Injective e) (B : ℕ) (hB : ∀ j, e j ≤ B)
    (f : J → MvPolynomial I K) (hf : ∀ j, (f j).totalDegree ≤ 1) :
    (weightedGraph e f).natDegree ≤ B ∧ ∀ i, ((weightedGraph e f).coeff i).totalDegree ≤ 1 := by
  classical
  refine ⟨Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ =>
    (Polynomial.natDegree_monomial_le _).trans (hB j)), fun i => ?_⟩
  by_cases h : i ∈ Set.range e
  · obtain ⟨j,rfl⟩ := h
    rw [weightedGraph_coeff e he]
    exact hf _
  · have hn (j) : e j ≠ i := fun h' => h ⟨j,h'⟩
    simp [weightedGraph, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, hn]

variable {ι : Type*} {h : ℕ} [Fintype ι]

/-- The graph equations enforce both the output coefficients and the selected coordinate pins. -/
noncomputable def fiberResiduals (c : ι → K) (s : Finset (Fin (h+1))) (a : Fin (h+1) → K) :
    ι ⊕ s → MvPolynomial (Option (Fin h) ⊕ ι) K :=
  Sum.elim (fun j => X (.inr j) - C (c j))
    (fun i => X (.inl ((_root_.finSuccEquiv h) i.val)) - C (a i.val))

omit [Fintype ι] in
/-- The full graph base locus of these residuals is a finite set whenever the pinned
fiber in the parameter chart is finite. -/
theorem finite_residual_base {E : Type*} [Field E] [Algebra E K]
    (Y : ι → MvPolynomial (Fin h) K) (c : ι → K) (k : Option (Fin h))
    (s : Finset (Fin (h+1))) (a : Fin (h+1) → E)
    (hpin : (VPVNP.SliceGeometry.pinnedPoints (graphFiber Y c k) s a).Finite) :
    {w ∈ zeroLocus K (RingHom.ker (graphChartMap Y k)) |
      ∀ j, eval w (fiberResiduals c s (algebraMap E K ∘ a) j) = 0}.Finite := by
  let expand (z : Fin (h+1) → K) := Sum.elim (z ∘ (_root_.finSuccEquiv h).symm) c
  apply (hpin.image expand).subset
  intro w hw
  let z := fun i : Fin (h+1) => w (.inl ((_root_.finSuccEquiv h) i))
  have he : expand z = w := by
    funext j
    cases j with
    | inl i => simp [expand, z]
    | inr i =>
      change c i = w (.inr i)
      exact (sub_eq_zero.mp (by simpa [fiberResiduals] using hw.2 (.inl i))).symm
  refine ⟨z, ⟨?_, ?_⟩, he⟩
  · change expand z ∈ zeroLocus K (RingHom.ker (graphChartMap Y k))
    rw [he]; exact hw.1
  · intro i hi
    exact sub_eq_zero.mp (by simpa [z, fiberResiduals] using hw.2 (.inr ⟨i,hi⟩))

omit [Fintype ι] in
/-- All fiber residuals are affine-linear, so no output degree is incurred in the
incidence algebra before composing with the parametrization. -/
theorem fiberResiduals_degree (c : ι → K) (s : Finset (Fin (h+1))) (a : Fin (h+1) → K)
    (j : ι ⊕ s) : (fiberResiduals c s a j).totalDegree ≤ 1 := by
  cases j with
  | inl j => exact (totalDegree_sub_C_le ..).trans (totalDegree_X _).le
  | inr i => exact (totalDegree_sub_C_le ..).trans (totalDegree_X _).le

end Branch

end BorderVNP
end Computability
end OAI
