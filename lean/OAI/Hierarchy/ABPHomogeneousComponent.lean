import OAI.Hierarchy.ABPLinearCombination
import OAI.Hierarchy.ABPScale
import OAI.Hierarchy.ABPDegree
import OAI.Hierarchy.Interpolation

namespace OAI
/-! # Extracting a homogeneous component of an algebraic branching program -/

namespace Hierarchy
open MvPolynomial
noncomputable section

/-- Over an infinite field, one homogeneous component of a size-`s` affine ABP
has an affine ABP of size at most `(s+2)^2`. -/
theorem HasABP.homogeneousComponent {F : Type*} {σ : Type} [Field F] [Infinite F] [Fintype σ]
    {s : ℕ} {p : MvPolynomial σ F} (h : HasABP s p) (d : ℕ) :
    HasABP ((s + 2) ^ 2) (MvPolynomial.homogeneousComponent d p) := by
  classical
  obtain ⟨g, rfl, size⟩ := h
  obtain ⟨S, c, card, expansion⟩ :=
    homogeneousComponent_interpolation g.polynomial d s (g.totalDegree_le_size.trans size)
  obtain ⟨out, value, cost⟩ := ABP.linearCombination S c (fun t => g.scaleVars t) s
    (fun t _ => (g.size_scaleVars t).le.trans size)
  refine ⟨out, ?_, ?_⟩
  · rw [expansion]
    simpa only [ABP.polynomial_scaleVars] using value
  · apply cost.trans
    simp only [card, pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega


end
end Hierarchy

end OAI
