import OAI.LinearAlgebra.SpectralBooks.ConeTranslate

/-!
# Euclidean flats spanned by orthogonal axes

In a CAT(0) cone, suppose the two unit endpoints of each marked axis are
opposite and every pairing between different axes vanishes. Successive
translations along the axes realize the Euclidean inner product on their
span. This proves the flat construction in Lemma `axis-rigidity`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open HyperbolicObstruction
open scoped BigOperators

section

variable {X : Type*} [MetricSpace X] {D : ℕ}

/-- Translate the cone vertex in the coordinate directions from a finite
set. The resulting map has the prescribed scalar products, and the unused
axes remain orthogonal to every point in its image. -/
private theorem exists_partial_flat (T : ConeData X) (h : CATZero X)
    (x : Fin D → Bool → X) (hunit : ∀ i a, T.normSq (x i a) = 1)
    (hopp : ∀ i, T.Opposite (x i false) (x i true))
    (hcross : ∀ i j, i ≠ j → ∀ a b, T.pairing (x i a) (x j b) = 0)
    (s : Finset (Fin D)) :
    ∃ f : EuclideanSpace ℝ (Fin D) → X,
      (∀ u v, T.pairing (f u) (f v) = ∑ i ∈ s, u i * v i) ∧
      ∀ j ∉ s, ∀ b u, T.pairing (x j b) (f u) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ ↦ T.vertex, by simp, ?_⟩
    intro j _ b u
    exact (T.pairing_comm _ _).trans (T.pairing_vertex _)
  | @insert i s hi ih =>
    obtain ⟨f, hdot, horth⟩ := ih
    refine ⟨fun u ↦ signedTranslate T h (x i false) (x i true) (u i) (f u), ?_, ?_⟩
    · intro u v
      rw [pairing_signedTranslates_of_orthogonal T h (hopp i) (hunit i false)
        (horth i hi false u) (horth i hi true u) (horth i hi false v) (horth i hi true v),
        hdot, Finset.sum_insert hi, add_comm]
    · intro j hj b u
      have hji : j ≠ i := fun he ↦ hj (Finset.mem_insert.mpr (Or.inl he))
      have hjs : j ∉ s := fun hs ↦ hj (Finset.mem_insert_of_mem hs)
      have hp : T.Parallel (x i false) (x i true) (x j b) := by
        simp [ConeData.Parallel, hcross i j hji.symm]
      have hfu : T.Parallel (x i false) (x i true) (f u) := by
        simp [ConeData.Parallel, horth i hi]
      rw [pairing_signedTranslate T h (hopp i) hp hfu,
        horth j hjs, hcross i j hji.symm, mul_zero, add_zero]

/-- A finite collection of opposite unit pairs which are orthogonal across
different axes spans an isometrically embedded Euclidean space. -/
theorem exists_isometry_of_orthogonal_axes (T : ConeData X) (h : CATZero X)
    (x : Fin D → Bool → X) (hunit : ∀ i a, T.normSq (x i a) = 1)
    (hopp : ∀ i, T.Opposite (x i false) (x i true))
    (hcross : ∀ i j, i ≠ j → ∀ a b, T.pairing (x i a) (x j b) = 0) :
    ∃ f : EuclideanSpace ℝ (Fin D) → X, Isometry f := by
  obtain ⟨f, hdot, _⟩ := exists_partial_flat T h x hunit hopp hcross Finset.univ
  refine ⟨f, Isometry.of_dist_eq fun u v ↦ ?_⟩
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [T.dist_sq, ← T.pairing_self, ← T.pairing_self, hdot, hdot, hdot,
    EuclideanSpace.dist_sq_eq, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [Real.dist_eq, sq_abs]; ring

end

end SpectralBooks
end LinearAlgebra
end OAI
