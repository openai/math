import OAI.LinearAlgebra.SpectralBooks.Book.BookMarginal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! # The increment on the old page

Independence removes the opposite-page point from the difference of prices.
The flat law on the original chart and invariance of mean width under
translation and isometric embedding then give the required lifted increment.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace Book

open Set
open scoped Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def horizontalLinearIsometry : E →ₗᵢ[ℝ] Lift E where
  toFun := horizontal
  map_add' u v := by
    apply WithLp.ofLp_injective 2
    change (u + v, (0 : ℝ)) = (u + v, 0 + 0)
    simp
  map_smul' r u := by
    apply WithLp.ofLp_injective 2
    change (r • u, (0 : ℝ)) = (r • u, r • 0)
    simp
  norm_map' v := by simp [horizontal]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem meanWidth_centeredHorizontal (T : Finset E) (hT : T.Nonempty) (y : E) :
    meanWidth (T.image fun z => horizontal (z - y)) (hT.image _) = meanWidth T hT := by
  have h := meanWidth_linearIsometry (horizontalLinearIsometry (E := E))
    (T.image (· + -y)) (hT.image _)
  rw [meanWidth_translate T hT] at h
  change meanWidth ((T.image (· + -y)).image horizontal) _ = _ at h
  simpa only [Finset.image_image, Function.comp_def, sub_eq_add_neg] using h

/-- The finite old configuration includes the center `y`, the points of `C`
in the chart, and the point `x` in the other page. -/
def oldConfiguration {X : Type*} (c : E → X) (x : X) (C : Finset E) (y : E) : Finset X :=
  insert x ((insert y C).image c)

/-- The `hflat` identity of the outward increment. The additive constant
`k` is the price of adjoining `x` over the corners, independent of the
other chart sites by equation `eq:book-independence`. -/
theorem price_increment_on_old_page {X : Type*}
    (δ : Finset X → ℝ) (c : E → X) (x : X) {U : Set E} (C : Finset E) (k : ℝ)
    (hC : (C : Set E) ⊆ U)
    (hflat : ∀ T : Finset E, ∀ hT : T.Nonempty, (T : Set E) ⊆ U →
      δ (T.image c) = meanWidth T hT)
    (hind : ∀ T : Finset E, C ⊆ T → (T : Set E) ⊆ U →
      δ (insert x (T.image c)) = δ (T.image c) + k)
    (y e : E) (h : ℝ) (hy : y ∈ U) (hz : y + h • e ∈ U) :
    δ (insert (c (y + h • e)) (oldConfiguration c x C y)) - δ (oldConfiguration c x C y) =
      meanWidth (insert (h • horizontal e) (centeredCorners C y)) (Finset.insert_nonempty _ _) -
        meanWidth (centeredCorners C y) (Finset.insert_nonempty _ _) := by
  let T := insert y C
  let z := y + h • e
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  have hCT : C ⊆ T := Finset.subset_insert _ _
  have hTU : (T : Set E) ⊆ U := by simpa [T] using Set.insert_subset hy hC
  have hzU : (↑(insert z T) : Set E) ⊆ U := by simpa only [Finset.coe_insert] using Set.insert_subset hz hTU
  have hOld := hind T hCT hTU
  have hNew := hind (insert z T) (hCT.trans (Finset.subset_insert _ _)) hzU
  have hW := meanWidth_centeredHorizontal T hT y
  have hW' := meanWidth_centeredHorizontal (insert z T) (Finset.insert_nonempty _ _) y
  have hA : T.image (fun w => horizontal (w - y)) = centeredCorners C y := by
    simpa only [T, Finset.image_insert, sub_self] using
      show insert (horizontal (0 : E)) (C.image fun w => horizontal (w - y)) = centeredCorners C y from rfl
  have hB : (insert z T).image (fun w => horizontal (w - y)) =
      insert (h • horizontal e) (centeredCorners C y) := by
    rw [Finset.image_insert, hA]
    congr 1
    change horizontal (y + h • e - y) = h • horizontal e
    simp [horizontal, ← WithLp.toLp_smul]
  rw [show meanWidth (centeredCorners C y) (Finset.insert_nonempty _ _) = meanWidth T hT by
    simpa only [hA] using hW]
  rw [show meanWidth (insert (h • horizontal e) (centeredCorners C y)) (Finset.insert_nonempty _ _) =
      meanWidth (insert z T) (Finset.insert_nonempty _ _) by simpa only [hB] using hW']
  rw [← hflat T hT hTU, ← hflat (insert z T) (Finset.insert_nonempty _ _) hzU]
  change δ (insert (c z) (insert x (T.image c))) - δ (insert x (T.image c)) = _
  rw [Finset.insert_comm, ← Finset.image_insert, hOld, hNew]
  ring

variable {X : Type*}

/-- The contracted configuration at fraction `t`, based at the chart point `y`. -/
def contractedSites (γ : X → X → ℝ → X) (y : X) (P : Finset X) (t : ℝ) : Finset X :=
  insert y (P.image fun q => γ y q t)

/-- Contracting occupied sites toward an occupied center costs nothing to
adjoin. Each contraction lies between two of the original sites. -/
theorem price_union_contractedSites (δ : Finset X → ℝ) (γ : X → X → ℝ → X)
    (hseg : ∀ (T : Finset X) (u v : X), u ∈ T → v ∈ T → ∀ t ∈ Icc (0 : ℝ) 1,
      δ (insert (γ u v t) T) = δ T)
    (P : Finset X) {y : X} (hy : y ∈ P) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    δ (P ∪ contractedSites γ y P t) = δ P := by
  have h (T : Finset X) (hT : T ⊆ P) : δ (P ∪ T.image (fun q => γ y q t)) = δ P := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert q T _ ih =>
      rw [Finset.image_insert, Finset.union_insert, hseg _ y q
        (Finset.mem_union_left _ hy)
        (Finset.mem_union_left _ (hT (Finset.mem_insert_self _ _))) _ ht]
      exact ih ((Finset.subset_insert _ _).trans hT)
  unfold contractedSites
  rw [Finset.union_insert, Finset.insert_eq_of_mem (Finset.mem_union_left _ hy)]
  exact h P (Finset.Subset.refl _)

end Book

end

end SpectralBooks
end LinearAlgebra
end OAI
