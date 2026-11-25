import OAI.LinearAlgebra.SpectralBooks.FinitePriceSpace
import OAI.LinearAlgebra.SpectralBooks.GeodesicExtensionTower
import OAI.LinearAlgebra.SpectralBooks.GridPriceSelection

/-! # Realizing the selected grid prices as metric spaces

Every selected grid price is realized on a finite metric spectral space over
the same field. A CAT(0) extension preserving all its prices then gives the
spaces and the two grids in the book construction.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open HyperbolicObstruction
section
open SiteTensor

variable {F : Type*} [Field F]

/-- The finite wire-metric quotient realizes all raw evaluations of a spectral
price on a finite set of labels, including the zero price. -/
theorem IsSpectralPrice.exists_finite_metric_realization {I : Type} [Fintype I] [Nontrivial I]
    {g : NonzeroProduct.{0} I F →+ ℝ} (hg : IsSpectralPrice unit_le_nonzeroClass g) :
    ∃ (A : FinitePriceSpace F) (p : I → A.carrier), Function.Surjective p ∧
      ∀ T : Raw.{0} I F, A.prices.price T p = classPrice g (ofRaw T) := by
  have hrep : ∃ (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I F → _ → _)) (c : ℝ),
      0 ≤ c ∧ ∀ T : Raw.{0} I F, rawLogPrice φ c T = classPrice g (ofRaw T) := by
    rcases hg with rfl | ⟨φ, c, hc, rfl⟩
    · exact ⟨(spectrum_nonempty I F).to_subtype.some, 0, le_rfl, fun _ ↦ by simp [rawLogPrice]⟩
    · exact ⟨φ, c, hc.le, fun _ ↦ (classPrice_scaled_log _ _ _).symm⟩
  obtain ⟨φ, c, hc, hφ⟩ := hrep
  obtain ⟨X, m, P, j, hj, _, he⟩ := exists_metric_price_realization φ c hc
  let A : FinitePriceSpace F := ⟨X, m, Finite.of_surjective j hj, P⟩
  refine ⟨A, j, hj, fun T ↦ ?_⟩
  have h := he T id
  rw [hφ, ofRaw_eq_iff.mpr (Raw.group_id_equivalent T)] at h
  exact h

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-- From a Euclidean spectral space satisfying the flat law, produce the
selected prices on actual finite metric spaces at every mesh. -/
theorem exists_finite_realizedGridDoubling (H : SpectralPlacementPrices F (EuclideanSpace ℝ ι))
    (hflat : ∀ (S : Finset (EuclideanSpace ℝ ι)) (hS : S.Nonempty), H.diagonal S = meanWidth S hS) :
    ∃ (A : ℕ → FinitePriceSpace F), Nonempty (RealizedGridDoubling H (fun n ↦ (A n).prices)) := by
  let g (n : ℕ) := (exists_selected_gridPrice H hflat n).some
  have : Nonempty (coordinateCubeCorners ι 1) := (coordinateCubeCorners_nonempty ι 1).to_subtype
  choose A p _ hp using fun n ↦ (g n).spectral.exists_finite_metric_realization
  exact ⟨A, ⟨realizedGridDoublingOfSelected (fun n ↦ (A n).prices) g p hp⟩⟩

/-- A price-preserving CAT(0) enlargement of every finite spectral space gives
actual CAT(0) spaces containing the doubled grids at all mesh sizes. -/
theorem exists_catZero_realizedGridDoubling (H : SpectralPlacementPrices F (EuclideanSpace ℝ ι))
    (hflat : ∀ (S : Finset (EuclideanSpace ℝ ι)) (hS : S.Nonempty), H.diagonal S = meanWidth S hS)
    (extendPrice : ∀ (A : FinitePriceSpace F), Nonempty A.carrier →
      ∃ (Y : Type) (_ : MetricSpace Y) (Q : SpectralPlacementPrices F Y),
        CATZero Y ∧ Nonempty (PriceEmbedding A.prices Q)) :
    ∃ (X : ℕ → Type) (_ : ∀ n, MetricSpace (X n)) (Q : ∀ n, SpectralPlacementPrices F (X n)),
      (∀ n, CATZero (X n)) ∧ Nonempty (RealizedGridDoubling H Q) := by
  obtain ⟨A, ⟨G⟩⟩ := exists_finite_realizedGridDoubling H hflat
  choose X m Q hc embed using fun n ↦ extendPrice (A n) ⟨G.place n gridCenter⟩
  let e n := (embed n).some
  let p n := (e n).map ∘ G.place n
  refine ⟨X, m, Q, hc, ⟨⟨p, ?_, ?_, ?_⟩⟩⟩
  · exact fun n T ht ↦ ((e n).price T _).le.trans (G.upper n T ht)
  · exact fun n k T ht hs ↦ ((e n).price T _).trans (G.private_eq n k T ht hs)
  · exact fun n ↦ ((e n).price _ _).trans (G.joint_eq n)

end

end

end SpectralBooks
end LinearAlgebra
end OAI
