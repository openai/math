import OAI.Computability.BorderVNP.CoverFrameMixing
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Compactness of the averages on a homogeneous frame space

Small right translations move a continuous function little in the sup norm,
uniformly on a compact frame space. For a translation-equivariant contraction
the same bound holds for every Cesàro average. Open orbit maps then give
equicontinuity, so Arzelà–Ascoli supplies compactness in the sup norm.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CoverFrameMixing

open BoundedContinuousFunction Filter Finset Set
open scoped Topology

private theorem norm_iter_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E) (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (f : E) (j : ℕ) :
    ‖P^[j] f‖ ≤ ‖f‖ := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply']; exact (hP _).trans ih

/-- Averages of iterates of a contraction preserve the sup-norm bound. -/
theorem norm_mean_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E) (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (f : E) (n : ℕ) :
    ‖mean P f n‖ ≤ ‖f‖ := by
  rw [mean, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((n : ℝ) + 1)⁻¹ * ∑ j ∈ range (n+1), ‖f‖ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sum_le _ _).trans (sum_le_sum (fun j _ => norm_iter_le P hP f j))
    _ = _ := by simp [nsmul_eq_mul, inv_mul_cancel_left₀ (by positivity : (n:ℝ)+1≠0)]

private theorem mean_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E) (f g : E) (n : ℕ) :
    mean P (f - g) n = mean P f n - mean P g n := by
  have h (i : ℕ) : P^[i] (f - g) = P^[i] f - P^[i] g := by
    induction i with
    | zero => rfl
    | succ i ih => simp only [Function.iterate_succ_apply' P, ih, map_sub]
  simp only [mean, h, sum_sub_distrib, smul_sub]

variable {X G : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace G] [One G]

/-- Right translation of a bounded continuous function by a motion of the host. -/
noncomputable def translate (move : X → G → X) (hmove : Continuous (Function.uncurry move))
    (g : G) (f : X →ᵇ ℝ) : X →ᵇ ℝ :=
  mkOfCompact ⟨fun x => f (move x g), f.continuous.comp (hmove.comp (continuous_id.prodMk
    continuous_const))⟩

omit [One G] in
private theorem mean_translate (move : X → G → X) (hm : Continuous (Function.uncurry move))
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ))
    (heq : ∀ g f, P (translate move hm g f) = translate move hm g (P f))
    (g : G) (f : X →ᵇ ℝ) (n : ℕ) :
    mean P (translate move hm g f) n = translate move hm g (mean P f n) := by
  have h (j : ℕ) : P^[j] (translate move hm g f) = translate move hm g (P^[j] f) := by
    induction j with
    | zero => rfl
    | succ j ih => simp only [Function.iterate_succ_apply' P, ih, heq]
  ext x
  simp only [mean, h]
  simp [translate, BoundedContinuousFunction.sum_apply]

/-- Translation equivariance of the operator controls all translated Cesàro averages. -/
theorem averages_equicontinuous (move : X → G → X) (hm : Continuous (Function.uncurry move))
    (h1 : ∀ x, move x 1 = x) (hop : ∀ x, IsOpenMap (move x))
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)) (hP : ∀ f, ‖P f‖ ≤ ‖f‖)
    (heq : ∀ g f, P (translate move hm g f) = translate move hm g (P f)) (f : X →ᵇ ℝ) :
    Equicontinuous (fun (n : ℕ) (x : X) => mean P f n x) := by
  intro x
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  let good : Set (X × G) := {p | dist (f p.1) (f (move p.1 p.2)) < ε}
  have ho : IsOpen good := isOpen_lt ((f.continuous.comp continuous_fst).dist
    (f.continuous.comp hm)) continuous_const
  obtain ⟨U, V, _, hv, hu, hone, huv⟩ := generalized_tube_lemma isCompact_univ
    (isCompact_singleton (x := (1:G))) ho (by
      rintro ⟨x,g⟩ ⟨_, rfl : g = 1⟩; simpa [good, h1] using hε)
  have hs : move x '' V ∈ 𝓝 x := (hop x V hv).mem_nhds ⟨1, hone rfl, h1 _⟩
  filter_upwards [hs] with y hy
  obtain ⟨g, hg, rfl⟩ := hy
  intro n
  have hdist : dist f (translate move hm g f) < ε :=
    (BoundedContinuousFunction.dist_lt_iff_of_compact hε).mpr
      (fun z => huv (show (z, g) ∈ U ×ˢ V from ⟨hu (mem_univ z), hg⟩))
  calc
    dist (mean P f n x) (mean P f n (move x g))
      ≤ dist (mean P f n) (translate move hm g (mean P f n)) :=
        BoundedContinuousFunction.dist_coe_le_dist (f := mean P f n) (g := translate move hm g (mean P f n)) x
    _ = ‖mean P (f - translate move hm g f) n‖ := by
      rw [← mean_translate move hm P heq, dist_eq_norm, mean_sub]
    _ ≤ ‖f - translate move hm g f‖ := norm_mean_le P hP _ _
    _ < ε := by rwa [← dist_eq_norm]

/-- Relative compactness in the uniform norm of all the frame averages. -/
theorem averages_compact (move : X → G → X) (hm : Continuous (Function.uncurry move))
    (h1 : ∀ x, move x 1 = x) (hop : ∀ x, IsOpenMap (move x))
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)) (hP : ∀ f, ‖P f‖ ≤ ‖f‖)
    (heq : ∀ g f, P (translate move hm g f) = translate move hm g (P f)) (f : X →ᵇ ℝ) :
    IsCompact (closure (Set.range (mean P f))) := by
  apply BoundedContinuousFunction.arzela_ascoli (Icc (-‖f‖) ‖f‖) isCompact_Icc
  · rintro _ x ⟨n, rfl⟩
    have h := (BoundedContinuousFunction.norm_coe_le_norm (mean P f n) x).trans
      (norm_mean_le P hP f n)
    exact abs_le.mp h
  · intro x
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    filter_upwards [(Metric.equicontinuousAt_iff_right.mp
      (averages_equicontinuous move hm h1 hop P hP heq f x)) ε hε] with y h
    rintro ⟨_,n,rfl⟩
    exact h n

end CoverFrameMixing

end BorderVNP
end Computability
end OAI
