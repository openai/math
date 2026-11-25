import OAI.LinearAlgebra.SpectralBooks.DoubledGridPrices
import OAI.LinearAlgebra.SpectralBooks.DiagonalProduct
import OAI.LinearAlgebra.SpectralBooks.SpectralDiagonal

/-! # From the tensor evaluations in the doubling theorem to the finite grids

All three comparison prices come from the same Euclidean spectral space. The
resulting tensor evaluations, after isometric extension, give the input to the
metric and diagonal ultralimit constructions.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
section
open SiteTensor

variable {ι : Type} [Fintype ι] {F : Type*} [Field F] {X : ℕ → Type*} [∀ n, MetricSpace (X n)]

/-- Place the binary diagonal on the specified labels, with scalar slots at all other labels. -/
def gridSupportDiagonal (F : Type*) [Field F] {n : ℕ} (S : Finset (DoubledGridSite ι n)) :
    Raw.{0} (DoubledGridSite ι n) F := (Raw.diagonal S F (Fin 2)).group Subtype.val

theorem gridSupportDiagonal_ne_zero {n : ℕ} {S : Finset (DoubledGridSite ι n)} (hS : S.Nonempty) :
    (gridSupportDiagonal F S).coeff ≠ 0 := by
  apply (Raw.group_ne_zero_iff ..).mpr
  intro he
  obtain ⟨i, hi⟩ := hS
  have h := congrFun he (fun _ ↦ (0 : Fin 2))
  rw [Raw.diagonal_coeff_at (⟨i, hi⟩ : S)] at h
  rw [ite_eq_left (fun _ ↦ rfl)] at h
  exact one_ne_zero (α := F) h

/-- A privately supported diagonal has scalar coordinate spaces outside the private grid. -/
theorem gridSupportDiagonal_private {n : ℕ} {S : Finset (DoubledGridSite ι n)} {k : Bool}
    (hs : S ⊆ gridLabels ι n k) (i : DoubledGridSite ι n) (hi : i ∉ gridLabels ι n k) :
    Subsingleton ((gridSupportDiagonal F S).Leg i) := by
  have : IsEmpty {j : S // (j : DoubledGridSite ι n) = i} :=
    ⟨fun j ↦ hi (j.property ▸ hs j.val.property)⟩
  exact inferInstanceAs (Subsingleton ({j : S // (j : DoubledGridSite ι n) = i} → Fin 2))

/-- The candidate upper price on tensors is the sum of the three original placed prices. -/
def sumGridTensorPrices (H : SpectralPlacementPrices F (EuclideanSpace ℝ ι))
    {n : ℕ} (T : Raw.{0} (DoubledGridSite ι n) F) : ℝ :=
  H.price T (gridPlacement none) + H.price T (gridPlacement (some false)) +
    H.price T (gridPlacement (some true))

/-- Tensor evaluations supplied by doubling at `λ = 1` and an extension preserving them.
The global inequality applies to all nonzero tensors. Private tensors, and the full
diagonal on the two grids with the auxiliary sites excluded, attain equality. -/
structure RealizedGridDoubling (H : SpectralPlacementPrices F (EuclideanSpace ℝ ι))
    (Q : ∀ n, SpectralPlacementPrices F (X n)) where
  place : ∀ n, DoubledGridSite ι n → X n
  upper : ∀ n (T : Raw.{0} (DoubledGridSite ι n) F), T.coeff ≠ 0 →
    (Q n).price T (place n) ≤ sumGridTensorPrices H T
  private_eq : ∀ n k (T : Raw.{0} (DoubledGridSite ι n) F), T.coeff ≠ 0 →
    (∀ i ∉ gridLabels ι n k, Subsingleton (T.Leg i)) →
    (Q n).price T (place n) = sumGridTensorPrices H T
  joint_eq : ∀ n, let T := gridSupportDiagonal F (gridLabels ι n false ∪ gridLabels ι n true)
    (Q n).price T (place n) = sumGridTensorPrices H T

/-- The grouped diagonal has the price of the occupied set, including collisions. -/
theorem gridSupport_price {n : ℕ} {Y : Type*} [MetricSpace Y] [DecidableEq Y]
    (P : SpectralPlacementPrices F Y) (S : Finset (DoubledGridSite ι n)) (hS : S.Nonempty)
    (p : DoubledGridSite ι n → Y) : P.price (gridSupportDiagonal F S) p = P.diagonal (S.image p) := by
  let : Nonempty S := hS.to_subtype
  rw [gridSupportDiagonal, ← P.group, P.price_binaryDiagonal_eq]
  congr 1
  ext t
  simp

/-- The flat law computes the target on every grid-label diagonal, including colliding placements. -/
theorem sumGridTensorPrices_gridSupport {n : ℕ} (H : SpectralPlacementPrices F (EuclideanSpace ℝ ι))
    (hflat : ∀ (S : Finset (EuclideanSpace ℝ ι)) (hS : S.Nonempty), H.diagonal S = meanWidth S hS)
    (S : Finset (DoubledGridSite ι n)) (hS : S.Nonempty) :
    sumGridTensorPrices H (gridSupportDiagonal F S) = sumPlacedDiagonal S hS := by
  have h (p : Option Bool) : H.price (gridSupportDiagonal F S) (gridPlacement p) =
      meanWidth (S.image (gridPlacement p)) (hS.image _) :=
    by
      rw [gridSupport_price H S hS]
      exact hflat (S.image (gridPlacement p)) (hS.image (gridPlacement p))
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (h none) (h (some false))) (h (some true))

namespace RealizedGridDoubling

variable {H : SpectralPlacementPrices F (EuclideanSpace ℝ ι)} {Q : ∀ n, SpectralPlacementPrices F (X n)}

/-- After applying the Euclidean flat law, the realized tensor inequalities supply
all finite grid price hypotheses with the canonical binary diagonal of each space. -/
def gridPrices (G : RealizedGridDoubling H Q)
    (hflat : ∀ (S : Finset (EuclideanSpace ℝ ι)) (hS : S.Nonempty), H.diagonal S = meanWidth S hS)
    (hm : ∀ n ⦃S T⦄, S.Nonempty → S ⊆ T → (Q n).diagonal S ≤ (Q n).diagonal T)
    (hs : ∀ n, IntersectingSubmodular (Q n).diagonal) : DoubledGridPrices ι X where
  place := G.place
  diagonal n := (Q n).diagonal
  wire n := (Q n).diagonal_pair
  mono := hm
  submod := hs
  upper n S hS := by
    simpa only [gridSupport_price _ S hS, sumGridTensorPrices_gridSupport H hflat S hS] using
      G.upper n _ (gridSupportDiagonal_ne_zero hS)
  private_eq n k S hS hpriv := by
    simpa only [gridSupport_price _ S hS, sumGridTensorPrices_gridSupport H hflat S hS] using
      G.private_eq n k _ (gridSupportDiagonal_ne_zero hS) (gridSupportDiagonal_private hpriv)
  joint_eq n := by
    let S := gridLabels ι n false ∪ gridLabels ι n true
    have hS : S.Nonempty := (gridLabels_nonempty ι n false).mono Finset.subset_union_left
    exact (gridSupport_price (Q n) S hS _).symm.trans
      ((G.joint_eq n).trans (sumGridTensorPrices_gridSupport H hflat S hS))

end RealizedGridDoubling
end

end

end SpectralBooks
end LinearAlgebra
end OAI
