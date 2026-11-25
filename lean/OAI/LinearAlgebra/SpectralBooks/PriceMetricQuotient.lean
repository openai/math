import OAI.LinearAlgebra.SpectralBooks.SpectralSpace

/-! # Removing zero distances from spectral placements

The transport inequality makes finite tensor prices independent of the choice
of representatives of points of the metric separation quotient.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SpectralPlacementPrices

open SiteTensor

variable {X K : Type*} [PseudoMetricSpace X] [Field K]

private noncomputable def representative (x : SeparationQuotient X) : X :=
  (SeparationQuotient.surjective_mk x).choose

private theorem mk_representative (x : SeparationQuotient X) :
    SeparationQuotient.mk (representative x) = x :=
  (SeparationQuotient.surjective_mk x).choose_spec

private theorem isometry_representative : Isometry (representative (X := X)) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [← SeparationQuotient.dist_mk, mk_representative, mk_representative]

/-- Every pseudometric spectral placement descends to the metric quotient. -/
noncomputable def separationQuotient (P : SpectralPlacementPrices K X) :
    SpectralPlacementPrices K (SeparationQuotient X) :=
  P.pullback representative isometry_representative

/-- The quotient projection preserves the price of every finite placed tensor. -/
theorem separationQuotient_price (P : SpectralPlacementPrices K X)
    {I : Type} [Fintype I] (T : Raw.{0} I K) (x : I → X) :
    P.separationQuotient.price T (SeparationQuotient.mk ∘ x) = P.price T x := by
  let y := representative ∘ SeparationQuotient.mk ∘ x
  have hdist (i : I) : dist (y i) (x i) = 0 := by
    change dist (representative _) _ = 0
    rw [← SeparationQuotient.dist_mk, mk_representative]
    exact dist_self _
  have h := P.transport T y x
  change P.price T y = P.price T x
  simpa [hdist] using h

end SpectralPlacementPrices

end SpectralBooks
end LinearAlgebra
end OAI
