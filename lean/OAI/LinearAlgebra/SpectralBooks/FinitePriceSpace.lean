import OAI.LinearAlgebra.SpectralBooks.FinitePlacementDiameter
import OAI.LinearAlgebra.SpectralBooks.FinitePlacementNormalization
import OAI.LinearAlgebra.SpectralBooks.PriceMetricQuotient
import OAI.LinearAlgebra.SpectralBooks.TensorGroupCompose

/-! # A finite spectral price as a metric spectral space

The distance of two sites is the price of their binary wire. After quotienting
by distance zero, the metric space still realizes every original tensor price,
including placements with repeated sites.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

noncomputable section

open scoped NNReal
variable {J : Type} [Fintype J] [Nonempty J] {K : Type*} [Field K]
  (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
  (c : ℝ) (hc : 0 ≤ c)

/-- Binary wire distance gives a pseudometric on the original sites. -/
@[instance_reducible] def wirePseudoMetric : PseudoMetricSpace J where
  dist := rawWireDistance φ c
  dist_self := rawWireDistance_self φ c hc
  dist_comm := rawWireDistance_symm φ c
  dist_triangle := rawWireDistance_triangle φ c hc

/-- On the finite set of sites the price of each placement is the price of
the tensor obtained by grouping its indices. -/
def finitePlacementPrices : letI := wirePseudoMetric φ c hc; SpectralPlacementPrices K J := by
  letI := wirePseudoMetric φ c hc
  refine {
    price := fun T x => rawLogPrice φ c (T.group x)
    zero_tensor := fun T h x => rawLogPrice_zero φ c _ (by
      exact funext fun y => congrFun h _)
    collapsed := fun T s => rawLogPrice_const φ c hc T s
    group := fun T σ x => ?_
    wire := fun x => ?_
    transport := fun T x y => ?_
    dist_le_diagonal := fun x i j => rawWireDistance_le_group_diagonal φ hc x i j
    normalized := fun e => ?_
  }
  · unfold rawLogPrice
    rw [ofRaw_eq_iff.mpr (Raw.group_group_equivalent T σ x)]
  · show rawLogPrice φ c ((Raw.diagonal (Fin 2) K (Fin 2)).group x) =
      rawLogPrice φ c ((Raw.diagonal (Fin 2) K (Fin 2)).group ![x 0, x 1])
    have h : ![x 0, x 1] = x := by funext i; fin_cases i <;> rfl
    rw [h]
  · rw [Real.dist_eq]
    exact rawLogPrice_transport φ c hc T x y
  · obtain ⟨ψ, hψ⟩ := rawLogPrice_group_embedding φ e c
    exact ⟨ψ, fun T _ => hψ T⟩

include hc in
/-- Every finite spectral price over the field has a metric realization over
that same field, preserving all placed tensor prices and the binary wire distances. -/
theorem exists_metric_price_realization :
    ∃ (X : Type) (_ : MetricSpace X) (P : SpectralPlacementPrices K X) (ι : J → X),
      Function.Surjective ι ∧
      (∀ s t, dist (ι s) (ι t) = rawWireDistance φ c s t) ∧
      ∀ {I : Type} [Fintype I] (T : Raw.{0} I K) (p : I → J),
        P.price T (ι ∘ p) = rawLogPrice φ c (T.group p) := by
  let := wirePseudoMetric φ c hc
  let P := finitePlacementPrices φ c hc
  refine ⟨SeparationQuotient J, inferInstance, P.separationQuotient,
    SeparationQuotient.mk, SeparationQuotient.surjective_mk, SeparationQuotient.dist_mk, ?_⟩
  intro I _ T p
  exact P.separationQuotient_price T p

end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
