import OAI.LinearAlgebra.SpectralBooks.SpectralSpace
import OAI.LinearAlgebra.SpectralBooks.PriceLimit
import OAI.LinearAlgebra.SpectralBooks.ConcreteSpectrum

/-!
# Spectral prices on metric blowups

All placed tensors on all finite site sets use one ultrafilter. A finite
placement of distinct sites stays injective eventually, so compactness of the
normalized spectrum in its original tensor semiring supplies its limiting
spectral point. The completed CAT(0) tangent cone is such a blowup.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace SpectralPlacementPrices

open Filter Topology HyperbolicObstruction SiteTensor

variable {K X Y L : Type*} [Field K] [PseudoMetricSpace X] [MetricSpace Y]

/-- Spectral placement prices on a space whose distances are ultralimits of
rescaled distances in a family of spectral spaces. -/
def blowupFamily {Z : L → Type*} [∀ i, PseudoMetricSpace (Z i)]
    (H : ∀ i, SpectralPlacementPrices K (Z i))
    (u : Ultrafilter L) (scale : L → ℝ) (hs : ∀ i, 0 < scale i)
    (point : ∀ i, Y → Z i) (y₀ : Y)
    (hdist : ∀ p q, Tendsto (fun i => dist (point i p) (point i q) / scale i)
      (u : Filter L) (𝓝 (dist p q))) :
    SpectralPlacementPrices K Y := by
  have spec {I : Type} [Fintype I] (T : Raw.{0} I K) :=
    blowupPriceFamily_spec u scale hs point y₀ hdist _ (fun i => (H i).price T)
      (fun i => (H i).collapsed T) (fun i => (H i).transport T)
  refine {
    price := fun T => blowupPriceFamily u scale point (fun i => (H i).price T)
    zero_tensor := ?_
    collapsed := fun T => (spec T).2.1
    group := fun T σ => blowupPriceFamily_reindex u scale point σ _ _ (fun i => (H i).group T σ)
    wire := ?_
    transport := fun T => (spec T).2.2
    dist_le_diagonal := ?_
    normalized := ?_ }
  · intro I _ T h x
    apply tendsto_nhds_unique ((spec T).1 x)
    simpa only [fun i => (H i).zero_tensor T h, zero_div] using
      (tendsto_const_nhds (x := (0 : ℝ)) : Tendsto _ (u : Filter L) _)
  · intro x
    rw [show (fun i => (H i).price (Raw.diagonal (Fin 2) K (Fin 2))) =
        (fun i (y : Fin 2 → Z i) => dist (y 0) (y 1)) from
      funext fun i => funext (H i).wire]
    exact blowupPriceFamily_wire u scale point hdist x
  · intro I _ x a b
    apply le_of_tendsto_of_tendsto (hdist (x a) (x b)) ((spec _).1 x)
    exact Eventually.of_forall fun i => div_le_div_of_nonneg_right
      ((H i).dist_le_diagonal (point i ∘ x) a b) (hs i).le
  · intro I _ _ x
    let R := {T : Raw.{0} I K // T.coeff ≠ 0}
    obtain ⟨ψ, hψ⟩ := blowupPriceFamily_spectral (fun a b : TensorClass.{0} I K => a ≤ b) exists_le_natCast
      u scale point hdist (fun T : R => ofRaw T.val)
      (fun T => ofRaw_one_le_of_nonzero T.val T.prop)
      (fun i => (H i).price (Raw.diagonal I K (Fin 2))) (fun (T : R) i => (H i).price T.val)
      (fun i x hx => by
        obtain ⟨φ, hφ⟩ := (H i).normalized ⟨x, hx⟩
        exact ⟨φ, fun T => hφ T.val T.prop⟩)
      x x.injective ((spec _).1 x) (fun T => (spec T.val).1 x)
    exact ⟨ψ, fun T hT => hψ ⟨T, hT⟩⟩

/-- Representatives of a placement compute the price of its tensor in the
resulting spectral space, jointly along the given ultrafilter. -/
theorem tendsto_blowupFamily_price {Z : L → Type*} [∀ i, PseudoMetricSpace (Z i)]
    (H : ∀ i, SpectralPlacementPrices K (Z i)) (u : Ultrafilter L)
    (scale : L → ℝ) (hs : ∀ i, 0 < scale i) (point : ∀ i, Y → Z i) (y₀ : Y)
    (hdist : ∀ p q, Tendsto (fun i => dist (point i p) (point i q) / scale i)
      (u : Filter L) (𝓝 (dist p q)))
    {A : Type} [Fintype A] (T : Raw.{0} A K) (p : A → Y) :
    Tendsto (fun i => (H i).price T (point i ∘ p) / scale i) (u : Filter L)
      (𝓝 ((blowupFamily H u scale hs point y₀ hdist).price T p)) :=
  (blowupPriceFamily_spec u scale hs point y₀ hdist _ (fun i => (H i).price T)
    (fun i => (H i).collapsed T) (fun i => (H i).transport T)).1 p

/-- Spectral placement prices on a space whose distances are ultralimits of
rescaled distances in a spectral space. -/
def blowup (H : SpectralPlacementPrices K X)
    (u : Ultrafilter L) (scale : L → ℝ) (hs : ∀ i, 0 < scale i)
    (point : L → Y → X) (y₀ : Y)
    (hdist : ∀ p q, Tendsto (fun i => dist (point i p) (point i q) / scale i)
      (u : Filter L) (𝓝 (dist p q))) :
    SpectralPlacementPrices K Y :=
  blowupFamily (fun _ => H) u scale hs point y₀ hdist

/-- The completed metric tangent cone carries spectral prices over the original
field. Representatives are chosen jointly for all its points and independently
of the local tensor formats. -/
def tangentCone {Z : Type*} [MetricSpace Z] (H : SpectralPlacementPrices K Z)
    (h : CATZero Z) (o : Z) : SpectralPlacementPrices K (TangentCone h o) := by
  classical
  apply Classical.choice
  obtain ⟨s, f, hs, _, _, hd⟩ := tangentCone_pointed_approx h o
  let u := Ultrafilter.of (atTop : Filter (Finset (TangentCone h o) × ℕ))
  exact ⟨H.blowup u s hs f (TangentCone.vertex h o)
    (fun p q => (hd p q).mono_left (Ultrafilter.of_le _))⟩

end SpectralPlacementPrices

end

end SpectralBooks
end LinearAlgebra
end OAI
