import OAI.LinearAlgebra.SpectralBooks.AffinePatch
import OAI.LinearAlgebra.SpectralBooks.AngularWidth
import OAI.LinearAlgebra.SpectralBooks.PatchPullback
import OAI.LinearAlgebra.SpectralBooks.CenteredFlatLaw
import Mathlib.Data.Finset.Preimage

/-! # The flat diagonal law on an arbitrary convex Euclidean patch -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set
open scoped Classical RealInnerProductSpace
noncomputable section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- On every convex Euclidean patch satisfying the diagonal price laws, the
price of a nonempty finite configuration equals its normalized Gaussian mean width. -/
theorem flatDiagonalLaw {C : Set E} {δ : Finset E → ℝ} (H : DiagonalPriceLawsOn C δ)
    (hC : Convex ℝ C) (S : Finset E) (hS : S.Nonempty) (hSC : (S : Set E) ⊆ C) :
    δ S = meanWidth S hS := by
  let K := convexHull ℝ (S : Set E)
  have hSK : (S : Set E) ⊆ K := subset_convexHull ℝ (S : Set E)
  have hKC : K ⊆ C := convexHull_min hSC hC
  obtain ⟨i, hrange, hint⟩ := exists_centered_affinePatch (convex_convexHull ℝ (S : Set E))
    (hS.to_set.mono hSK)
  let P := S.preimage i i.injective.injOn
  have himage : P.image i = S := by
    rw [Finset.image_preimage]
    exact Finset.filter_eq_self.mpr fun _ hx ↦ hrange (hSK hx)
  have h0K : (0 : (affineSpan ℝ K).direction) ∈ i ⁻¹' K := interior_subset hint
  have hup : (↑(insert 0 P) : Set (affineSpan ℝ K).direction) ⊆ i ⁻¹' C := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hKC h0K
    · exact hSC (Finset.mem_preimage.mp hx)
  have hh := centeredFlatDiagonalLaw (H.comp_affineIsometry i) (hC.affine_preimage i.toAffineMap)
    (interior_mono (Set.preimage_mono hKC) hint) (insert 0 P) (Finset.mem_insert_self _ _) hup
  have hi : (insert 0 P).image i = insert (i 0) S := by rw [Finset.image_insert, himage]
  have hprice := H.jointlyConvex.price_insert_of_mem_convexHull hC
    (fun _ _ _ h _ ↦ H.monotone h) S hS hSC h0K
  calc
    δ S = δ ((insert 0 P).image i) := by rw [hi, hprice]
    _ = meanWidth (insert 0 P) (Finset.insert_nonempty _ _) := hh
    _ = meanWidth ((insert 0 P).image i) ((Finset.insert_nonempty _ _).image _) :=
      (meanWidth_affineIsometry i _ (Finset.insert_nonempty _ _)).symm
    _ = meanWidth S hS := by
      have hmem : (({i 0} : Finset E) : Set E) ⊆ K := by
        simp only [Finset.coe_singleton, Set.singleton_subset_iff]
        exact h0K
      simpa only [hi, Finset.union_singleton] using meanWidth_union_of_subset_convexHull hS hmem

end

end SpectralBooks
end LinearAlgebra
end OAI
