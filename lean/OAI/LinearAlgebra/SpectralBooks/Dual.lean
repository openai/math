import OAI.LinearAlgebra.SpectralBooks.DualNorming
import OAI.LinearAlgebra.SpectralBooks.DualHull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Extending the crossing inequality to the dual ball

For fixed weights the sum of the squared norms on the two crossing cuts is jointly
convex and continuous. It therefore obeys any uniform bound on the product
of the closed convex hulls of the test functionals.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A uniform crossing bound on test vectors extends to their closed convex hull. -/
theorem crossingBound_closure_convexHull (S : Set E) (t u C : ℝ)
    (h : ∀ f ∈ S, ∀ g ∈ S, ‖t • f + u • g‖ ^ 2 + ‖t • f - u • g‖ ^ 2 ≤ C)
    {f g : E} (hf : f ∈ closure (convexHull ℝ S)) (hg : g ∈ closure (convexHull ℝ S)) :
    ‖t • f + u • g‖ ^ 2 + ‖t • f - u • g‖ ^ 2 ≤ C := by
  let plus : E × E →ₗ[ℝ] E := t • LinearMap.fst ℝ E E + u • LinearMap.snd ℝ E E
  let minus : E × E →ₗ[ℝ] E := t • LinearMap.fst ℝ E E - u • LinearMap.snd ℝ E E
  let A := {p : E × E | ‖t • p.1 + u • p.2‖ ^ 2 + ‖t • p.1 - u • p.2‖ ^ 2 ≤ C}
  have hsq : ConvexOn ℝ univ (fun x : E ↦ ‖x‖ ^ 2) :=
    convexOn_univ_norm.pow (fun _ _ ↦ norm_nonneg _) 2
  have hplus : ConvexOn ℝ univ (fun p : E × E ↦ ‖plus p‖ ^ 2) := hsq.comp_linearMap plus
  have hminus : ConvexOn ℝ univ (fun p : E × E ↦ ‖minus p‖ ^ 2) := hsq.comp_linearMap minus
  have hc : Convex ℝ A := by
    simpa [A, plus, minus] using (hplus.add hminus).convex_le C
  have hclosed : IsClosed A := isClosed_le (by fun_prop) continuous_const
  have hp : (f, g) ∈ closure (convexHull ℝ (S ×ˢ S)) := by
    rw [convexHull_prod, closure_prod_eq]
    exact ⟨hf, hg⟩
  exact closure_minimal (convexHull_min (fun p hp ↦ h p.1 hp.1 p.2 hp.2) hc) hclosed hp

variable [FiniteDimensional ℝ E] [Nontrivial E]

/-- The dual unit ball is the closed convex hull of the derivatives at smooth unit vectors. -/
theorem closure_convexHull_smoothNormDerivatives :
    closure (convexHull ℝ (smoothNormDerivatives E)) = Metric.closedBall 0 1 := by
  apply Subset.antisymm
  · apply closure_minimal _ Metric.isClosed_closedBall
    apply convexHull_min _ (convex_closedBall ..)
    intro f hf
    simpa using smoothNormDerivatives_norm_le_one hf
  · exact fun _ hf ↦ mem_closure_convexHull_of_norming
      (fun x _ hr ↦ exists_smoothNormDerivative_gt x hr) (by simpa using hf)

/-- The crossing-dual inequality at smooth unit vectors controls all dual vectors
of norm at most one, with the same weights and bound. -/
theorem dualBall_crossingBound_of_smooth (t u : ℝ)
    (h : ∀ (x y : E) (f g : E →L[ℝ] ℝ), ‖x‖ = 1 → ‖y‖ = 1 →
      HasFDerivAt (fun z : E ↦ ‖z‖) f x → HasFDerivAt (fun z : E ↦ ‖z‖) g y →
      ‖t • f + u • g‖ ^ 2 + ‖t • f - u • g‖ ^ 2 ≤ 2 * (t ^ 2 + u ^ 2))
    (f g : E →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1) :
    ‖t • f + u • g‖ ^ 2 + ‖t • f - u • g‖ ^ 2 ≤ 2 * (t ^ 2 + u ^ 2) := by
  apply crossingBound_closure_convexHull (smoothNormDerivatives E) t u
  · rintro a ⟨x, hx, ha⟩ b ⟨y, hy, hb⟩
    exact h x y a b hx hy ha hb
  · simpa [closure_convexHull_smoothNormDerivatives] using hf
  · simpa [closure_convexHull_smoothNormDerivatives] using hg

end SpectralBooks
end LinearAlgebra
end OAI
