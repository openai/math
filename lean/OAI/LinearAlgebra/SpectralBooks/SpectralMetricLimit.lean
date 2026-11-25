import OAI.LinearAlgebra.SpectralBooks.PriceBlowup
import OAI.LinearAlgebra.SpectralBooks.MetricLimitPrice

/-! # Spectral structure on the pointed ultralimit of varying spectral spaces

Using the coordinate representatives with unit scale in the spectral blowup
construction puts spectral prices on the separated metric ultralimit.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace SpectralPlacementPrices

open Filter Topology HyperbolicObstruction MetricLimit SiteTensor

variable {K : Type*} [Field K] {X : ℕ → Type*} [∀ n, MetricSpace (X n)] {o : ∀ n, X n}

private def rep {U : Ultrafilter ℕ} (x : Space (U := U) (X := X) (o := o)) : Bounded U X o :=
  (SeparationQuotient.surjective_mk x).choose

private theorem point_rep {U : Ultrafilter ℕ} (x : Space (U := U) (X := X) (o := o)) :
    point (rep x) = x := (SeparationQuotient.surjective_mk x).choose_spec

/-- All tensor prices on the actual separated ultralimit of the varying
pointed spaces `(X n, o n)`. -/
def metricLimit (U : Ultrafilter ℕ) (P : ∀ n, SpectralPlacementPrices K (X n)) :
    SpectralPlacementPrices K (Space (U := U) (X := X) (o := o)) :=
  blowupFamily P U (fun _ ↦ 1) (fun _ ↦ zero_lt_one) (fun n x ↦ (rep x).val n)
    (point (⟨o, 0, by simp⟩ : Bounded U X o))
    (fun x y ↦ by simpa only [div_one, point_rep] using tendsto_point_dist (rep x) (rep y))

/-- The ultralimit prices simultaneously agree with the limits on every
bounded representative of every finite placed tensor. -/
theorem metricLimit_price_tendsto (U : Ultrafilter ℕ) (P : ∀ n, SpectralPlacementPrices K (X n))
    {I : Type} [Fintype I] (T : Raw.{0} I K) (p : I → Bounded U X o) :
    Tendsto (fun n ↦ (P n).price T (fun i ↦ (p i).val n)) (U : Filter ℕ)
      (𝓝 ((metricLimit U P).price T (point ∘ p))) := by
  change Tendsto _ _ (𝓝 (limUnder (U : Filter ℕ)
    (fun n ↦ (P n).price T (fun i ↦ (rep (point (p i))).val n) / 1)))
  simp only [div_one]
  exact tendsto_metricLimitPrice _ _ (fun n ↦ (P n).collapsed T) (fun n ↦ (P n).transport T) p

end SpectralPlacementPrices

end

end SpectralBooks
end LinearAlgebra
end OAI
