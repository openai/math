import OAI.LinearAlgebra.SpectralBooks.PatchPrice
import OAI.LinearAlgebra.SpectralBooks.PlacementConvexity
import OAI.LinearAlgebra.SpectralBooks.Increment
import OAI.LinearAlgebra.SpectralBooks.TangentPrice

/-! # Structural properties of tangent diagonal prices

Blowing up a patch at an interior point preserves its finite price
inequalities and makes the limiting price homogeneous.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open Filter
open scoped Topology Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}
    {δ D : Finset E → ℝ} {y : E}

theorem IsTangentPriceAt.monotone (ht : IsTangentPriceAt δ y D) (hy : y ∈ interior C)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → (T : Set E) ⊆ C → δ S ≤ δ T)
    ⦃S T : Finset E⦄ (hS : S.Nonempty) (hST : S ⊆ T) : D S ≤ D T := by
  apply le_of_tendsto_of_tendsto (ht S hS) (ht T (hS.mono hST))
  filter_upwards [self_mem_nhdsWithin, eventually_patch_image_subset hy T] with h (hh : 0 < h) hTC
  apply div_le_div_of_nonneg_right _ hh.le
  exact hmono (hS.image _) (Finset.image_subset_image hST) hTC

theorem IsTangentPriceAt.intersectingSubmodular (ht : IsTangentPriceAt δ y D)
    (hy : y ∈ interior C)
    (hsubmod : ∀ ⦃A B : Finset E⦄, (A : Set E) ⊆ C → (B : Set E) ⊆ C → (A ∩ B).Nonempty →
      δ (A ∪ B) + δ (A ∩ B) ≤ δ A + δ B) :
    IntersectingSubmodular D := by
  intro A B hI
  have hA := hI.mono Finset.inter_subset_left
  have hB := hI.mono Finset.inter_subset_right
  have hU := hA.mono (Finset.subset_union_left (s₂ := B))
  apply le_of_tendsto_of_tendsto ((ht _ hU).add (ht _ hI)) ((ht _ hA).add (ht _ hB))
  filter_upwards [self_mem_nhdsWithin, eventually_patch_image_subset hy A,
    eventually_patch_image_subset hy B] with h (hh : 0 < h) hAC hBC
  let g := fun x : E ↦ y + h • x
  have hinj : Function.Injective g := (add_right_injective y).comp (smul_right_injective E hh.ne')
  have heq := Finset.image_inter A B hinj
  have hsub := hsubmod hAC hBC (heq ▸ hI.image g)
  simp only [← add_div]
  apply div_le_div_of_nonneg_right _ hh.le
  change δ ((A ∪ B).image g) + δ ((A ∩ B).image g) ≤ _
  rw [Finset.image_union, heq]
  exact hsub

theorem IsTangentPriceAt.jointlyConvex (ht : IsTangentPriceAt δ y D)
    (hy : y ∈ interior C) (hj : JointlyConvexPriceOn C δ) : JointlyConvexPrice D := by
  intro P hP a b ha hb hab
  let M (p : E × E) := a • p.1 + b • p.2
  apply le_of_tendsto_of_tendsto (ht (P.image M) (hP.image _))
    (((ht (P.image Prod.fst) (hP.image _)).const_mul a).add
      ((ht (P.image Prod.snd) (hP.image _)).const_mul b))
  filter_upwards [self_mem_nhdsWithin, eventually_patch_image_subset hy (P.image Prod.fst),
    eventually_patch_image_subset hy (P.image Prod.snd)] with h (hh : 0 < h) h₁ h₂
  let g := fun x : E ↦ y + h • x
  let mapPair := fun p : E × E ↦ (g p.1, g p.2)
  have hin : ∀ p ∈ P.image mapPair, p.1 ∈ C ∧ p.2 ∈ C := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨h₁ (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hq)),
      h₂ (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hq))⟩
  have hineq := hj (P.image mapPair) (hP.image _) hin a b ha hb hab
  have hmap (p : E × E) : a • (g p.1) + b • (g p.2) = g (M p) := by
    dsimp [g, M]
    rw [smul_add, smul_add, smul_add, smul_comm a h, smul_comm b h]
    calc
      _ = (a • y + b • y) + (h • a • p.1 + h • b • p.2) := by abel
      _ = _ := by rw [← add_smul, hab, one_smul]
  simp only [Finset.image_image, Function.comp_def, mapPair, hmap] at hineq
  change δ ((P.image M).image g) / _ ≤ a * (δ ((P.image Prod.fst).image g) / _) +
    b * (δ ((P.image Prod.snd).image g) / _)
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
  apply div_le_div_of_nonneg_right _ hh.le
  simpa only [Finset.image_image, Function.comp_def] using hineq

theorem IsTangentPriceAt.homogeneous (ht : IsTangentPriceAt δ y D)
    (S : Finset E) (hS : S.Nonempty) (t : ℝ) (htpos : 0 < t) :
    D (S.image (t • ·)) = t * D S := by
  have hlim := tangentPrice_rescale (f := fun h : ℝ ↦ δ (S.image fun x ↦ y + h • x))
    (ht S hS) htpos
  apply tendsto_nhds_unique (ht _ (hS.image _))
  simpa only [Finset.image_image, Function.comp_def, smul_smul, mul_comm t] using hlim

end

end

end SpectralBooks
end LinearAlgebra
end OAI
