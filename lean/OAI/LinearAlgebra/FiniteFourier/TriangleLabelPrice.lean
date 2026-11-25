import OAI.LinearAlgebra.FiniteFourier.PhasePrice
import OAI.LinearAlgebra.SpectralBooks.SpectralDiagonal
import OAI.LinearAlgebra.SpectralBooks.TriangleWidth

/-!
# A common label on a triangle

The price of an arbitrary finite label is the binary price multiplied by
its base-two logarithmic dimension. This computation applies when sites coincide.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical NNReal

variable {K : Type*} {X : Type} [Field K] [MetricSpace X]

/-- A common label on any finite placement, whose sites may coincide. -/
theorem placed_diagonal_log_card (P : SpectralPlacementPrices K X)
    {I : Type} [Fintype I] [Nonempty I] (x : I → X) (O : Type) [Fintype O] :
    P.price (Raw.diagonal I K O) x =
      P.price (Raw.diagonal I K (Fin 2)) x * Real.logb 2 (Fintype.card O) := by
  rcases placed_price_normalized_or_collapsed P x with hc | ⟨φ, c, _, he⟩
  · simp only [hc, zero_mul]
  · have eval (A : Type) [Fintype A] : φ.val (ofRaw (Raw.diagonal I K A)) =
        (Fintype.card A : ℝ≥0) := by
      rw [ofRaw_diagonal_eq_natCast]
      exact map_natCast (normalizedSpectrum.toRingHom φ) _
    simp only [he, rawLogPrice, eval, NNReal.coe_natCast, Fintype.card_fin,
      Nat.cast_ofNat, NNReal.coe_ofNat, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]

noncomputable local instance triangleLabelPriceDecidableEq : DecidableEq Plane := Classical.decEq _

private theorem triangle_range (a b z : Plane) :
    Finset.univ.image (![a,b,z] : Fin 3 → Plane) = {a,b,z} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

/-- The three-site price in the common-label construction is logarithmic
dimension times Euclidean semiperimeter. -/
theorem triangle_label_price (P : SpectralPlacementPrices K Plane)
    (hflat : ∀ (S : Finset Plane) (hS : S.Nonempty), P.diagonal S = meanWidth S hS)
    (O : Type) [Fintype O] (a b z : Plane) :
    P.price (Raw.diagonal (Fin 3) K O) ![a,b,z] =
      (dist a b + dist a z + dist b z) / 2 * Real.logb 2 (Fintype.card O) := by
  rw [placed_diagonal_log_card, P.price_binaryDiagonal_eq, triangle_range,
    hflat _ (Finset.insert_nonempty _ _), meanWidth_triangle, dist_comm z a]
  ring

end FiniteFourier
end LinearAlgebra
end OAI
