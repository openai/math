import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! # Determining a sphere measure from half-line projections -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory Metric Set
open scoped InnerProductSpace

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "S" => sphere (0 : E) 1

/-- The projected laws on closed negative hemispheres determine a finite sphere measure.
The opposite direction recovers the positive hemisphere. -/
theorem sphereMeasure_eq_of_negative_projection (ξ η : Measure S)
    [IsFiniteMeasure ξ] [IsFiniteMeasure η]
    (h : ∀ z : E, (ξ.restrict {x : S | ⟪(x : E), z⟫_ℝ ≤ 0}).map (fun x : S ↦ ⟪(x : E), z⟫_ℝ)
      = (η.restrict {x : S | ⟪(x : E), z⟫_ℝ ≤ 0}).map (fun x : S ↦ ⟪(x : E), z⟫_ℝ)) :
    ξ = η := by
  let p (z : E) (x : S) := ⟪(x : E), z⟫_ℝ
  have hp (z : E) : Measurable (p z) := (continuous_subtype_val.inner continuous_const).measurable
  have hneg (z : E) : (ξ.map (p z)).restrict (Iic 0) = (η.map (p z)).restrict (Iic 0) := by
    rw [Measure.restrict_map (hp z) measurableSet_Iic, Measure.restrict_map (hp z) measurableSet_Iic]
    simpa [p, preimage, Iic] using h z
  have hpos (z : E) : (ξ.map (p z)).restrict (Ici 0) = (η.map (p z)).restrict (Ici 0) := by
    have H := congrArg (Measure.map (fun t : ℝ ↦ -t)) (h (-z))
    rw [Measure.map_map measurable_neg (hp (-z)), Measure.map_map measurable_neg (hp (-z))] at H
    rw [Measure.restrict_map (hp z) measurableSet_Ici, Measure.restrict_map (hp z) measurableSet_Ici]
    simpa [p, Function.comp_def, preimage, Ici] using H
  have hproj (z : E) : ξ.map (p z) = η.map (p z) := by
    have H := Measure.restrict_union_congr.mpr ⟨hneg z, hpos z⟩
    simpa using H
  apply (MeasurableEmbedding.subtype_coe (isClosed_sphere (x := (0 : E)) (ε := 1)).measurableSet).map_injective
  apply Measure.ext_of_charFun
  funext z
  rw [charFun_map_eq_charFun_map_inner_one measurable_subtype_coe.aemeasurable,
    charFun_map_eq_charFun_map_inner_one (μ := η) measurable_subtype_coe.aemeasurable]
  exact congrArg (fun μ : Measure ℝ ↦ charFun μ 1) (hproj z)

end

end SpectralBooks
end LinearAlgebra
end OAI
