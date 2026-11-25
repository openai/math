import OAI.Computability.BorderVNP.ShortenEpochDirections
import OAI.Computability.BorderVNP.ShortenEpochProduct
import OAI.Computability.BorderVNP.CrossingNetwork

/-!
# Placing a profiled crossing at the representative center

Scale the Euclidean gadget by half the segment length, embed its axes by
the signed factor directions and move the resulting product configuration
to the chosen center. Its ordinary and selector wires retain at least
the Euclidean saving after paying for a separate hook at each port.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open Finset

universe u

variable {I : Type*} [Fintype I] {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}

/-- Moving the standard point to the chosen center by a translation and
positive scaling in each upper half-plane. -/
noncomputable def shiftTo (center x : HyperbolicHost I) : HyperbolicHost I :=
  WithLp.toLp 2 fun i => (center i).re +ᵥ
    ((⟨(center i).im, (center i).im_pos⟩ : {a : ℝ // 0 < a}) • (x i))

/-- Center shifts preserve the product metric exactly. -/
theorem shiftTo_isometry (center : HyperbolicHost I) : Isometry (shiftTo center) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [PiLp.dist_eq_sum (p := 2) (by norm_num), PiLp.dist_eq_sum (p := 2) (by norm_num)]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [show dist (shiftTo center x i) (shiftTo center y i) = dist (x i) (y i) from
    ((UpperHalfPlane.isometry_real_vadd (center i).re).comp
      (UpperHalfPlane.isometry_pos_mul ⟨(center i).im, (center i).im_pos⟩)).dist_eq _ _]

omit [Fintype I] in
/-- The origin of the translated tangent chart is the actual representative center. -/
theorem shiftTo_chart_zero (center : HyperbolicHost I) :
    shiftTo center (productChart 0) = center := by
  ext1 i
  apply UpperHalfPlane.ext_re_im
  · change ((center i).re +ᵥ ((⟨(center i).im, (center i).im_pos⟩ : {a : ℝ // 0 < a}) •
      tangentChart 0)).re = _
    simp [tangentChart, timeCoord, UpperHalfPlane.vadd_re, UpperHalfPlane.pos_real_re]
  · change ((center i).re +ᵥ ((⟨(center i).im, (center i).im_pos⟩ : {a : ℝ // 0 < a}) •
      tangentChart 0)).im = _
    simp [tangentChart, timeCoord, UpperHalfPlane.vadd_im, UpperHalfPlane.pos_real_im]

/-- The Euclidean gadget axes embed as the orthonormal signed factor permutations
of the representative tangent direction. -/
noncomputable def crossingAxes (u : Direction D ℂ) (hu : ‖u‖ = 1) :
    EuclideanSpace ℝ (Fin D) →ₗᵢ[ℝ] Direction D ℂ := by
  let basis := EuclideanSpace.basisFun (Fin D) ℝ
  let f := basis.toBasis.constr ℝ (fun j => signedFlip j u)
  apply f.isometryOfOrthonormal (v := basis.toBasis) basis.orthonormal
  have h : f ∘ basis.toBasis = fun j => signedFlip j u :=
    funext fun j => basis.toBasis.constr_basis ℝ _ j
  rw [h]
  exact signedFlip_orthonormal u hu

/-- The image of a positive axis terminal is its prescribed direction. Negative
terminals follow by linearity of the embedding. -/
theorem crossingAxes_axis (u : Direction D ℂ) (hu : ‖u‖ = 1) (j : Fin D) :
    crossingAxes u hu (EuclideanSpace.single j 1) = signedFlip j u := by
  change (EuclideanSpace.basisFun (Fin D) ℝ).toBasis.constr ℝ (fun j => signedFlip j u)
      (EuclideanSpace.single j 1) = _
  rw [← EuclideanSpace.basisFun_apply]
  exact (EuclideanSpace.basisFun (Fin D) ℝ).toBasis.constr_basis ℝ _ j

/-- Actual weighted wire cost after placing all sites of one profile in the host. -/
noncomputable def placedCost {H : Type*} [PseudoMetricSpace H] (N : Crossing.Network D P bits)
    (place : N.Site → H) :
    ℝ := ∑ e : N.Edge, (N.width e : ℝ) * dist (place (N.src e)) (place (N.dst e))

/-- Actual hook cost, including a separate hook of the whole port width for
each displaced external terminal. -/
noncomputable def hookCost {H : Type*} [PseudoMetricSpace H] (N : Crossing.Network D P bits)
    (place : N.Site → H) (actual : P → H) : ℝ :=
  ∑ p, (bits p : ℝ) * dist (actual p) (place (N.attach p))

/-- A strict profile saving in the Euclidean unit ball survives uniform
rescaling, embedding into any product tangent plane, translation to any
representative center, and terminal displacements. This single radius works
for every number of copies and every term histogram of the identity. -/
theorem place_profile_saving {ν : ℝ} (hν : 0 < ν) :
    ∃ h > 0, ∀ s ∈ Set.Icc (0 : ℝ) h, ∀ {D : ℕ} {P : Type u} [Fintype P] {bits : P → ℕ}
      (N : Crossing.Network D P bits)
      (axes : EuclideanSpace ℝ (Fin D) →ₗᵢ[ℝ] PiLp 2 (fun _ : I => ℂ))
      (center : HyperbolicHost I) (actual : P → HyperbolicHost I),
      let total := ∑ p, (bits p : ℝ)
      let place := fun v => shiftTo center (productChart (s • axes (N.position v)))
      let canonical := fun p => shiftTo center (productLine (axes (N.position (N.attach p))) s)
      N.cost ≤ (1 - ν) * total →
      (∀ p, dist (actual p) (canonical p) ≤ (ν / 4) * s) →
      placedCost N place + hookCost N place actual ≤ (1 - ν / 2) * s * total := by
  obtain ⟨h, hh, hhook⟩ := uniform_product_hooks (I := I) (show 0 < ν / 4 by positivity)
  refine ⟨h, hh, ?_⟩
  intro s hs D P inst bits N axes center actual total place canonical hc ha
  have hwire : placedCost N place ≤ s * N.cost := by
    unfold placedCost Crossing.Network.cost
    rw [mul_sum]
    apply sum_le_sum
    intro e _
    dsimp only [place]
    rw [(shiftTo_isometry center).dist_eq, mul_left_comm s]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply (productChart_dist_le _ _).trans_eq
    rw [dist_smul₀, axes.isometry.dist_eq, Real.norm_eq_abs, abs_of_nonneg hs.1]
  have hport : hookCost N place actual ≤ (ν / 2 * s) * total := by
    dsimp only [hookCost, total]
    rw [mul_sum]
    apply sum_le_sum
    intro p _
    rw [mul_comm (ν / 2 * s)]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hx := hhook s hs (axes (N.position (N.attach p)))
      (by simpa using N.in_ball (N.attach p))
    have hcan : dist (canonical p) (place (N.attach p)) ≤ ν / 4 * s := by
      dsimp only [canonical, place]
      rw [(shiftTo_isometry center).dist_eq, dist_comm]
      exact hx
    linarith only [dist_triangle (actual p) (canonical p) (place (N.attach p)), ha p, hcan]
  have hscaled := mul_le_mul_of_nonneg_left hc hs.1
  linarith only [hwire, hport, hscaled]

end Epoch

end BorderVNP
end Computability
end OAI
