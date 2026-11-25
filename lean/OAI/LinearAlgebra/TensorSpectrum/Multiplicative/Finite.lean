import OAI.LinearAlgebra.TensorSpectrum.Multiplicative.Projective

/-!
# Finite iteration through frozen affine slices

This is the finite induction in Appendix A.2. Its explicit local fixed-point
premise is the interface for the separately proved projective eigenstate theorem;
it is not an axiom or a completed character-existence result.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

open Set

variable {S : Type*} [CommMonoidWithZero S]

theorem finite_common_points_of_slice_fixedPoints
    (K : Set (S → ℝ)) (hK : K.Nonempty) (hcompact : IsCompact K)
    (hconvex : Convex ℝ K) (hunit : ∀ f ∈ K, f 1 = 1)
    (hpos : ∀ f ∈ K, ∀ z : S, z ≠ 0 → f z ≠ 0)
    (hinvariant : ∀ z : S, z ≠ 0 → MapsTo (projective z) K K)
    (hfixed : ∀ L : Set (S → ℝ), L ⊆ K → L.Nonempty → IsCompact L →
      Convex ℝ L → (∀ z : S, z ≠ 0 → MapsTo (projective z) L L) →
      ∀ z : S, z ≠ 0 → ∃ f ∈ L, projective z f = f) :
    ∀ F : Finset {z : S // z ≠ 0},
      ∃ f ∈ K, ∀ z ∈ F, f ∈ multiplicativeSet z.val := by
  classical
  have hslices : ∀ F : Finset {z : S // z ≠ 0},
      ∃ L : Set (S → ℝ), L ⊆ K ∧ L.Nonempty ∧ IsCompact L ∧ Convex ℝ L ∧
        (∀ z : S, z ≠ 0 → MapsTo (projective z) L L) ∧
        (∀ f ∈ L, ∀ z ∈ F, f ∈ multiplicativeSet z.val) := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      exact ⟨K, subset_rfl, hK, hcompact, hconvex, hinvariant, by simp⟩
    | @insert z F _ ih =>
      obtain ⟨L, hLK, hL, hLc, hLv, hLi, hLF⟩ := ih
      obtain ⟨f, hf, hfx⟩ := hfixed L hLK hL hLc hLv hLi z.val z.property
      let L' := L ∩ eigenSlice z.val (f z.val)
      have hfrozen := freeze_fixedPoint L z.val f hLc hLv hf hfx
        (hpos f (hLK hf) z.val z.property) hLi
      change f ∈ L' ∧ IsCompact L' ∧ Convex ℝ L' ∧
        (∀ w, w ≠ 0 → MapsTo (projective w) L' L') at hfrozen
      refine ⟨L', fun g hg => hLK hg.1, ⟨f, hfrozen.1⟩,
        hfrozen.2.1, hfrozen.2.2.1, hfrozen.2.2.2, ?_⟩
      intro g hg w hw
      rcases Finset.mem_insert.mp hw with hw | hw
      · rw [hw]
        exact eigenSlice_mem_multiplicativeSet z.val (f z.val) g hg.2
          (hunit g (hLK hg.1))
      · exact hLF g hg.1 w hw
  intro F
  obtain ⟨L, hLK, ⟨f, hf⟩, _, _, _, hLF⟩ := hslices F
  exact ⟨f, hLK hf, hLF f hf⟩

end OAI.LinearAlgebra.TensorSpectrum
