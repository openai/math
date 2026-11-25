import OAI.LinearAlgebra.FiniteFourier.RectanglePoint
import OAI.LinearAlgebra.SpectralBooks.SpectralFlatLaw

/-! # The common diagonal price of the four rectangle corners

The corner set is the Minkowski sum of its two centered axial segments.
Mean width is additive on that sum and agrees with length on each segment.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical Pointwise

local instance rectangleWidthDecidableEq : DecidableEq Plane := Classical.decEq _

private def xy (a b : ℝ) : Plane := WithLp.toLp 2 ![a,b]

private theorem xy_add (a b c d : ℝ) : xy a b + xy c d = xy (a+c) (b+d) := by
  ext i
  fin_cases i <;> rfl

private theorem dist_xy (a b c d : ℝ) :
    dist (xy a b) (xy c d) = Real.sqrt ((a-c)^2 + (b-d)^2) := by
  simp [xy, PiLp.dist_eq_of_L2, Fin.sum_univ_two, Real.dist_eq]

/-- Gaussian mean width of the four corner placement, including collapsed rectangles. -/
theorem meanWidth_rectangle {L W : ℝ} (hL : 0 ≤ L) (hW : 0 ≤ W) :
    meanWidth (Finset.univ.image (rectangleSites L W)) (Finset.univ_nonempty.image _) = L + W := by
  let A : Finset Plane := {xy (-W/2) 0, xy (W/2) 0}
  let B : Finset Plane := {xy 0 (L/2), xy 0 (-L/2)}
  have hA : A.Nonempty := Finset.insert_nonempty _ _
  have hB : B.Nonempty := Finset.insert_nonempty _ _
  have hcorners : Finset.univ.image (rectangleSites L W) = A + B := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_add, A, B,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact ⟨_, Or.inl rfl, _, Or.inl rfl, by rw [xy_add, add_zero, zero_add]; rfl⟩
      · exact ⟨_, Or.inr rfl, _, Or.inl rfl, by rw [xy_add, add_zero, zero_add]; rfl⟩
      · exact ⟨_, Or.inl rfl, _, Or.inr rfl, by rw [xy_add, add_zero, zero_add]; rfl⟩
      · exact ⟨_, Or.inr rfl, _, Or.inr rfl, by rw [xy_add, add_zero, zero_add]; rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        simp only [xy_add, add_zero, zero_add]
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩
  simp only [hcorners]
  calc
    meanWidth (A + B) (hA.add hB) = meanWidth A hA + meanWidth B hB := meanWidth_add A B hA hB
    _ = _ := by
      simp only [A, B, meanWidth_pair, dist_xy, sub_self, zero_pow (by decide : 2 ≠ 0),
        zero_add, add_zero, show -W/2-W/2 = -W by ring, show L/2 - -L/2 = L by ring,
        neg_sq, Real.sqrt_sq hL, Real.sqrt_sq hW]
      ring

variable {K : Type*} [Field K]

/-- The normalization of the character table rectangle follows from the plane's
flat diagonal law. -/
theorem rectangle_diagonal_price (P : SpectralPlacementPrices K Plane)
    (hflat : ∀ (S : Finset Plane) (hS : S.Nonempty), P.diagonal S = meanWidth S hS)
    {L W : ℝ} (hL : 0 ≤ L) (hW : 0 ≤ W) :
    P.price (Raw.diagonal (Fin 4) K (Fin 2)) (rectangleSites L W) = L + W := by
  rw [P.price_binaryDiagonal_eq]
  apply (hflat _ (Finset.univ_nonempty.image _)).trans
  exact meanWidth_rectangle hL hW

theorem exists_rectangle_point_of_flat_law (P : SpectralPlacementPrices K Plane)
    (hflat : ∀ (S : Finset Plane) (hS : S.Nonempty), P.diagonal S = meanWidth S hS)
    {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    ∃ φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 4) K → _ → Prop),
      ∀ (O I : Type) [Fintype O] [Fintype I] (M : Matrix O I K),
        (φ.val (ofRaw (phaseRaw M)) : ℝ) = rectangleValue (fourierPhasePrice P) M s c := by
  apply exists_rectangle_point P hs hc
  rw [rectangle_diagonal_price P hflat (by positivity) (by positivity)]
  ring

end

end

end FiniteFourier
end LinearAlgebra
end OAI
