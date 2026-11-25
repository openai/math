import OAI.LinearAlgebra.SpectralBooks.BookPlacement
import OAI.LinearAlgebra.SpectralBooks.GridTensorDoubling
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.GridPrivateFormat
import OAI.LinearAlgebra.SpectralBooks.GridDiagonalFormat

/-! # Applying tensor doubling to the three finite grids

The mean width of the original cube is positive. Its two private sides and its
joint diagonal have the same convex hull in the shared placement. This gives
the equality and positivity hypotheses for the tensor doubling theorem.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
section
open SiteTensor SiteTensor.BookFactors

variable {F : Type*} [Field F] {ι : Type} [Fintype ι]

/-- The tensor prices selected on one mesh, before the CAT(0) extension. -/
structure SelectedGridPrice (H : SpectralPlacementPrices F (EuclideanSpace ℝ ι)) (n : ℕ) where
  price : NonzeroProduct.{0} (DoubledGridSite ι n) F →+ ℝ
  spectral : IsSpectralPrice unit_le_nonzeroClass price
  upper : ∀ T : Raw.{0} (DoubledGridSite ι n) F, classPrice price (ofRaw T) ≤ sumGridTensorPrices H T
  private_eq : ∀ k (T : Raw.{0} (DoubledGridSite ι n) F), T.coeff ≠ 0 →
    (∀ i ∉ gridLabels ι n k, Subsingleton (T.Leg i)) → classPrice price (ofRaw T) = sumGridTensorPrices H T
  joint_eq : let T := gridSupportDiagonal F (gridLabels ι n false ∪ gridLabels ι n true)
    classPrice price (ofRaw T) = sumGridTensorPrices H T

private theorem price_congr_class {I : Type} [Fintype I] [Nonempty I] {X : Type*} [MetricSpace X]
    (H : SpectralPlacementPrices F X) {T V : Raw.{0} I F} (he : ofRaw T = ofRaw V) (x : I → X) :
    H.price T x = H.price V x := by
  obtain ⟨g, _, hg⟩ := H.exists_spectralPrice_of_placement x
  rw [hg, hg, he]

private theorem sumGridTensorPrices_congr {n : ℕ} (H : SpectralPlacementPrices F (EuclideanSpace ℝ ι))
    {T V : Raw.{0} (DoubledGridSite ι n) F} (h : ofRaw T = ofRaw V) : sumGridTensorPrices H T = sumGridTensorPrices H V := by
  unfold sumGridTensorPrices
  rw [price_congr_class H h, price_congr_class H h, price_congr_class H h]

/-- Apply doubling to the actual three placements in the original Euclidean spectral space. -/
theorem exists_selected_gridPrice [Nonempty ι] (H : SpectralPlacementPrices F (EuclideanSpace ℝ ι))
    (hflat : ∀ (S : Finset (EuclideanSpace ℝ ι)) (hS : S.Nonempty), H.diagonal S = meanWidth S hS)
    (n : ℕ) : Nonempty (SelectedGridPrice H n) := by
  let B := NoncentralGrid ι n
  let O := ↥(coordinateCubeCorners ι 1)
  let S := gridLabels ι n false ∪ gridLabels ι n true
  have hS : S.Nonempty := (gridLabels_nonempty ι n false).mono Finset.subset_union_left
  have hj : ofRaw (gridSupportDiagonal F S) = ofRaw (jointRaw F B B O) :=
    ofRaw_gridLabels_union_diagonal F ι n
  have hl : ofRaw (gridSupportDiagonal F (gridLabels ι n false)) = ofRaw ((privateDiagonal F B).leftRaw O B) :=
    ofRaw_gridLabels_false_diagonal F ι n
  have hjoint : H.price (jointRaw F B B O) (gridPlacement none) = innerCubeWidth ι := by
    rw [← price_congr_class H hj, gridSupport_price _ _ hS]
    exact (hflat _ (hS.image _)).trans (meanWidth_gridLabels_union ι n none)
  have hleft : H.price ((privateDiagonal F B).leftRaw O B) (gridPlacement none) = innerCubeWidth ι := by
    rw [← price_congr_class H hl, gridSupport_price _ _ (gridLabels_nonempty ι n false)]
    exact (hflat _ ((gridLabels_nonempty ι n false).image _)).trans (by simpa using meanWidth_gridLabels ι n none false)
  obtain ⟨g, hg, hu, heB, heC, hjoint'⟩ := doubling_of_placements H
    (gridPlacement (ι := ι) (n := n) none) (gridPlacement (some false)) (gridPlacement (some true))
    rfl rfl (by simp) (by simp) (by simp) (by simp)
    (hjoint.trans hleft.symm) (hleft ▸ innerCubeWidth_pos) 1 zero_le_one
  simp only [one_mul] at hu heB heC hjoint'
  refine ⟨⟨g, hg, hu, ?_, ?_⟩⟩
  · intro k T hT hsupport
    cases k
    · obtain ⟨p, hp⟩ := exists_privateData_left_of_subsingleton T hT
        (fun c ↦ hsupport _ (by simp [mem_gridLabels_false_iff, gridCenter]))
        (fun o ↦ hsupport _ (by simp [mem_gridLabels_false_iff, gridCenter]))
      change ofRaw (p.leftRaw O B) = ofRaw T at hp
      exact (congrArg (classPrice g) hp.symm).trans ((heB p).trans (sumGridTensorPrices_congr H hp))
    · obtain ⟨p, hp⟩ := exists_privateData_right_of_subsingleton T hT
        (fun b ↦ hsupport _ (by simp [mem_gridLabels_true_iff, gridCenter]))
        (fun o ↦ hsupport _ (by simp [mem_gridLabels_true_iff, gridCenter]))
      change ofRaw (p.rightRaw O B) = ofRaw T at hp
      exact (congrArg (classPrice g) hp.symm).trans ((heC p).trans (sumGridTensorPrices_congr H hp))
  · exact (congrArg (classPrice g) hj).trans (hjoint'.trans (sumGridTensorPrices_congr H hj.symm))

/-- Any price-preserving realization of the selected finite spectral prices gives the finite
configuration required for the CAT(0) and price ultralimits. -/
def realizedGridDoublingOfSelected {X : ℕ → Type*} [∀ n, MetricSpace (X n)]
    {H : SpectralPlacementPrices F (EuclideanSpace ℝ ι)} (Q : ∀ n, SpectralPlacementPrices F (X n))
    (g : ∀ n, SelectedGridPrice H n) (p : ∀ n, DoubledGridSite ι n → X n)
    (hp : ∀ n (T : Raw.{0} (DoubledGridSite ι n) F), (Q n).price T (p n) = classPrice (g n).price (ofRaw T)) :
    RealizedGridDoubling H Q where
  place := p
  upper n T _ := (hp n T).le.trans ((g n).upper _)
  private_eq n k T ht hs := (hp n T).trans ((g n).private_eq k T ht hs)
  joint_eq n := (hp n _).trans (g n).joint_eq

end

end

end SpectralBooks
end LinearAlgebra
end OAI
