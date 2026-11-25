import OAI.Optimization.LinearProgramming.Compression.Fiber
import OAI.Optimization.LinearProgramming.Compression.ProjectionRational

/-! Uniform projection onto the generator coordinates, followed by bounded rational
realization in the fiber. The two bounds are independent of the number of clipping rows. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators Matrix

variable {ι κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ] [DecidableEq σ]

private theorem fiber_transfer_system (A : Matrix ι κ ℚ) (b : ι → ℚ) (anchor : σ → κ)
    (x : σ → ℝ) (y : κ → ℝ) :
    (fiberRows A anchor).map (Rat.cast : ℚ → ℝ) *ᵥ y ≤
      (fun i => ((fiberConstant (σ := σ) b i : ℚ) : ℝ)) -
        (fiberParameter (ι := ι) (σ := σ) (K := ℚ)).map (Rat.cast : ℚ → ℝ) *ᵥ x ↔
      A.map (Rat.cast : ℚ → ℝ) *ᵥ y ≤ (fun i => (b i : ℝ)) ∧ ∀ j, y (anchor j) = x j := by
  have hc : (fun i => ((fiberConstant (σ := σ) b i : ℚ) : ℝ)) =
      fiberConstant (fun i => (b i : ℝ)) := by
    funext i
    cases i <;> simp [fiberConstant]
  rw [fiberRows_cast_real, fiberParameter_cast_real, hc, fiberConstant_sub_mulVec,
    fiberRows_mulVec_le_iff]

/-- If the old coordinates are in the projection of the full feasible region, preserving all
bounded integral affine comparisons puts the new coordinates in the projection as well. -/
theorem preserves_generator_fiber [Fintype ι] (A : Matrix ι κ ℚ) (b : ι → ℚ)
    (anchor : σ → κ) {B : ℕ} (hB : 1 ≤ B)
    (hA : ∀ i j, (A i j).num.natAbs ≤ B ∧ (A i j).den ≤ B)
    (hb : ∀ i, (b i).num.natAbs ≤ B ∧ (b i).den ≤ B)
    {x x' : σ → ℝ} (hx : ∃ y, A.map (Rat.cast : ℚ → ℝ) *ᵥ y ≤ (fun i => (b i : ℝ)) ∧
      ∀ j, y (anchor j) = x j)
    (tests : ∀ (a : σ → ℤ) (c : ℤ), (∀ j, (a j).natAbs ≤
        projectionCoefficientBound (Fintype.card κ)
          (clearedProjectionRowBound (Fintype.card σ) (Fintype.card κ) B)) →
      c.natAbs ≤ projectionCoefficientBound (Fintype.card κ)
        (clearedProjectionRowBound (Fintype.card σ) (Fintype.card κ) B) →
      (∑ j, (a j : ℝ) * x j) ≤ c → (∑ j, (a j : ℝ) * x' j) ≤ c) :
    ∃ y, A.map (Rat.cast : ℚ → ℝ) *ᵥ y ≤ (fun i => (b i : ℝ)) ∧ ∀ j, y (anchor j) = x' j := by
  obtain ⟨y, hy⟩ := hx
  have hform := (fiber_transfer_system A b anchor x y).mpr hy
  obtain ⟨y', hy'⟩ := rational_projection_of_preserving_affine_tests
    (fiberParameter (ι := ι) (σ := σ) (K := ℚ)) (fiberRows A anchor)
    (fiberConstant b) (B := B)
    (fun s j => ⟨(fiberParameter_height s j).1.trans hB, (fiberParameter_height s j).2.trans hB⟩)
    (fiberRows_height A anchor hB hA) (fun i => by
      cases i with
      | inl t => exact hb t
      | inr js => simpa [fiberConstant] using hB) ⟨y, hform⟩ tests
  exact ⟨y', (fiber_transfer_system A b anchor x' y').mp hy'⟩

end Compression
end LinearProgramming
end Optimization
end OAI
