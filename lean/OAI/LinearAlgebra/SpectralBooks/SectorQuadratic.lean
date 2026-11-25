import OAI.LinearAlgebra.SpectralBooks.FiniteMetricModel
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Topology.Algebra.SeparationQuotient.Basic
import Mathlib.Tactic

/-!
# The Euclidean distance identity in a seminormed sector

After taking the separated quotient of the sector seminorm, every finite
configuration of this normed space can be translated into the positive
quadrant. Consequently the manuscript's finite-configuration norm rigidity
criterion applies even when the sector has a kernel.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

private theorem finite_translate_quadrant {I : Type} [Fintype I] (p : I → ℝ × ℝ) :
    ∃ k : ℝ × ℝ, ∀ i, 0 ≤ p i + k := by
  classical
  refine ⟨(∑ i, |(p i).1|, ∑ i, |(p i).2|), fun i ↦ ⟨?_, ?_⟩⟩
  · have hs : |(p i).1| ≤ ∑ j, |(p j).1| := Finset.single_le_sum
      (fun j _ ↦ abs_nonneg (p j).1) (Finset.mem_univ i)
    change 0 ≤ (p i).1 + ∑ j, |(p j).1|
    linarith [neg_le_abs (p i).1]
  · have hs : |(p i).2| ≤ ∑ j, |(p j).2| := Finset.single_le_sum
      (fun j _ ↦ abs_nonneg (p j).2) (Finset.mem_univ i)
    change 0 ≤ (p i).2 + ∑ j, |(p j).2|
    linarith [neg_le_abs (p i).2]

private theorem seminorm_sq_of_quotient_rigidity {V : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (N : Seminorm ℝ V)
    (hquot : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (π : V →ₗ[ℝ] E), Function.Surjective π → (∀ z, ‖π z‖ = N z) →
      Nonempty (InnerProductSpace ℝ E))
    (x y : V) (s t : ℝ) :
    N (s • x - t • y) ^ 2 = s ^ 2 * N x ^ 2 + t ^ 2 * N y ^ 2 +
      s * t * (N (x-y) ^ 2 - N x ^ 2 - N y ^ 2) := by
  classical
  let := N.toAddGroupSeminorm.toSeminormedAddCommGroup
  let : NormedSpace ℝ V := ⟨fun a z ↦ (map_smul_eq_mul N a z).le⟩
  let E := SeparationQuotient V
  let π : V →ₗ[ℝ] E := (SeparationQuotient.mkCLM ℝ V).toLinearMap
  have hπ : Function.Surjective π := SeparationQuotient.surjective_mk
  let : FiniteDimensional ℝ E := FiniteDimensional.of_surjective π hπ
  have hnorm (z : V) : ‖π z‖ = N z := rfl
  have hpar : ∀ x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ =
      2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
    let : InnerProductSpace ℝ E := (hquot E π hπ hnorm).some
    exact parallelogram_law_with_norm_mul ℝ
  let : InnerProductSpace ℝ E := InnerProductSpace.ofNorm ℝ hpar
  simp only [← hnorm, map_sub, map_smul, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    real_inner_smul_left, real_inner_smul_right, mul_pow, sq_abs]
  ring

/-- Polarization of the sector seminorm. The expression at the right permits
computing the cosine coefficient from the three distances at parameter one. -/
theorem quadrant_seminorm_sq_of_rigidity {X : Type*} [MetricSpace X]
    (hX : SectorNormRigidity X) (H : ℝ × ℝ → X) (N : Seminorm ℝ (ℝ × ℝ))
    (hN : ∀ p q, 0 ≤ p → 0 ≤ q → dist (H p) (H q) = N (p - q))
    (x y : ℝ × ℝ) (s t : ℝ) :
    N (s • x - t • y) ^ 2 = s ^ 2 * N x ^ 2 + t ^ 2 * N y ^ 2 +
      s * t * (N (x-y) ^ 2 - N x ^ 2 - N y ^ 2) := by
  classical
  apply seminorm_sq_of_quotient_rigidity N _ x y s t
  intro E _ _ _ π hπ hnorm
  apply hX E
  intro I _ p
  choose v hv using fun i ↦ hπ (p i)
  obtain ⟨k, hk⟩ := finite_translate_quadrant v
  refine ⟨fun i ↦ H (v i + k), fun i j ↦ ?_⟩
  rw [hN _ _ (hk i) (hk j), add_sub_add_right_eq_sub, ← hv, ← hv, dist_eq_norm,
    ← map_sub, hnorm]

/-- Every finite set of coordinates can be moved into a patch by one translation
and positive dilation. If the pullback distances on this patch come from a seminorm,
scaled finite-configuration rigidity polarizes that seminorm on the entire plane. -/
theorem patch_seminorm_sq_of_rigidity {X : Type*} [MetricSpace X]
    (hX : ScaledSectorNormRigidity X) {C : Set (ℝ × ℝ)}
    (hfit : ∀ {I : Type} [Fintype I] (p : I → ℝ × ℝ),
      ∃ k : ℝ × ℝ, ∃ s : ℝ, 0 < s ∧ ∀ i, k + s • p i ∈ C)
    (H : ℝ × ℝ → X) (N : Seminorm ℝ (ℝ × ℝ))
    (hN : ∀ p ∈ C, ∀ q ∈ C, dist (H p) (H q) = N (p - q))
    (x y : ℝ × ℝ) (s t : ℝ) :
    N (s • x - t • y) ^ 2 = s ^ 2 * N x ^ 2 + t ^ 2 * N y ^ 2 +
      s * t * (N (x-y) ^ 2 - N x ^ 2 - N y ^ 2) := by
  classical
  apply seminorm_sq_of_quotient_rigidity N _ x y s t
  intro E _ _ _ π hπ hnorm
  apply hX E
  intro I _ p
  choose v hv using fun i ↦ hπ (p i)
  obtain ⟨k, s, hs, hk⟩ := hfit v
  refine ⟨s, hs, fun i ↦ H (k + s • v i), fun i j ↦ ?_⟩
  rw [hN _ (hk i) _ (hk j), add_sub_add_left_eq_sub, ← smul_sub, map_smul_eq_mul,
    Real.norm_of_nonneg hs.le, ← hv, ← hv, dist_eq_norm, ← map_sub, hnorm]

end SpectralBooks
end LinearAlgebra
end OAI
