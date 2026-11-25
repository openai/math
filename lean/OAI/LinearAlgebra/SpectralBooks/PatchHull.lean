import OAI.LinearAlgebra.SpectralBooks.PatchPrice

/-! # Finite convex hulls inside a patch

Keeping all occupied sites fixed and moving one extra index along a straight
segment yields the convexity of its price sublevel within the patch.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open scoped Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}
    {δ : Finset E → ℝ}

theorem JointlyConvexPriceOn.price_insert_of_mem_convexHull (hj : JointlyConvexPriceOn C δ)
    (hc : Convex ℝ C)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → (T : Set E) ⊆ C → δ S ≤ δ T)
    (S : Finset E) (hS : S.Nonempty) (hSC : (S : Set E) ⊆ C)
    {z : E} (hz : z ∈ convexHull ℝ (S : Set E)) : δ (insert z S) = δ S := by
  have hzC := convexHull_min hSC hc hz
  have hsub : (↑(insert z S) : Set E) ⊆ C := by
    rw [Finset.coe_insert]
    exact Set.insert_subset hzC hSC
  refine le_antisymm ?_ (hmono hS (Finset.subset_insert _ _) hsub)
  let L := {w : E | δ (insert w S) ≤ δ S}
  have hSL : (S : Set E) ⊆ C ∩ L := fun x hx ↦ ⟨hSC hx, by simp [L, Finset.insert_eq_of_mem hx]⟩
  suffices hCL : Convex ℝ (C ∩ L) from (convexHull_min hSL hCL hz).2
  intro x hx y hy a b ha hb hab
  refine ⟨hc hx.1 hy.1 ha hb hab, ?_⟩
  let P := S.image (fun s ↦ (s, s))
  have hin : ∀ p ∈ insert (x,y) P, p.1 ∈ C ∧ p.2 ∈ C := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact ⟨hx.1, hy.1⟩
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨hSC hs, hSC hs⟩
  have h := hj (insert (x,y) P) (Finset.insert_nonempty _ _) hin a b ha hb hab
  have hid (s : E) : a • s + b • s = s := by rw [← add_smul, hab, one_smul]
  simp [P, Finset.image_image, Function.comp_def, hid] at h
  change δ (insert (a • x + b • y) S) ≤ δ S
  calc
    _ ≤ a * δ (insert x S) + b * δ (insert y S) := h
    _ ≤ a * δ S + b * δ S := add_le_add
      (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
    _ = _ := by rw [← add_mul, hab, one_mul]

theorem JointlyConvexPriceOn.price_union_of_subset_convexHull (hj : JointlyConvexPriceOn C δ)
    (hc : Convex ℝ C)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → (T : Set E) ⊆ C → δ S ≤ δ T)
    (S T : Finset E) (hS : S.Nonempty) (hSC : (S : Set E) ⊆ C)
    (hT : (T : Set E) ⊆ convexHull ℝ (S : Set E)) : δ (S ∪ T) = δ S := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert z T hz ih =>
    have hT' : (T : Set E) ⊆ convexHull ℝ (S : Set E) :=
      fun _ hy ↦ hT (Finset.mem_insert_of_mem hy)
    have hsub : (S : Set E) ⊆ ↑(S ∪ T) := Finset.subset_union_left
    have hUC : (↑(S ∪ T) : Set E) ⊆ C := by
      simpa only [Finset.coe_union] using Set.union_subset hSC (hT'.trans (convexHull_min hSC hc))
    rw [Finset.union_insert, hj.price_insert_of_mem_convexHull hc hmono _
      (hS.mono Finset.subset_union_left) hUC (convexHull_mono hsub (hT (Finset.mem_insert_self z T))),
      ih hT']

end

end

end SpectralBooks
end LinearAlgebra
end OAI
