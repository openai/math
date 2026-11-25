import OAI.LinearAlgebra.FiniteFourier.Endpoint
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The kernel of a two-phase construction

The rows index the output registers and the columns index the input registers.
Expanding the two intermediate pairs of labels gives the contraction used
in the first-phase price estimate.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open scoped Classical Kronecker

variable {G K : Type*} [Fintype G] [Field K]

/-- The kernel of the circuit with first phase `H`, second phase `D`, and
three successive pairs of local maps. -/
def twoPhaseKernel (H D A₀ B₀ A₁ B₁ A₂ B₂ : Matrix G G K) : Matrix (G × G) (G × G) K :=
  (A₂ ⊗ₖ B₂) * phaseWidthZero D * (A₁ ⊗ₖ B₁) * phaseWidthZero H * (A₀ ⊗ₖ B₀)

/-- Expanding the circuit over the two intermediate register pairs. -/
theorem twoPhaseKernel_apply (H D A₀ B₀ A₁ B₁ A₂ B₂ : Matrix G G K) (x y : G × G) :
    twoPhaseKernel H D A₀ B₀ A₁ B₁ A₂ B₂ x y =
      ∑ i : G × G, ∑ j : G × G, D j.1 j.2 * H i.1 i.2 *
        A₀ i.1 y.1 * B₀ i.2 y.2 * A₁ j.1 i.1 * B₁ j.2 i.2 * A₂ x.1 j.1 * B₂ x.2 j.2 := by
  rw [twoPhaseKernel, phaseWidthZero_eq_diagonal, phaseWidthZero_eq_diagonal, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_diagonal]
  simp only [Matrix.kroneckerMap_apply]
  ring

/-- The Kronecker product of the two coordinate matrices realizes the product
of local changes of basis from the swap construction. -/
theorem localProduct_mulVec (A B : (G → K) ≃ₗ[K] (G → K)) (v : G × G → K) :
    (A.toLinearMap.toMatrix' ⊗ₖ B.toLinearMap.toMatrix').mulVec v = localProduct A B v := by
  have act (Q : (G → K) ≃ₗ[K] (G → K)) (u : G → K) (i : G) :
      Q u i = ∑ j, Q.toLinearMap.toMatrix' i j * u j :=
    congrFun (LinearMap.toMatrix'_mulVec Q.toLinearMap u).symm i
  funext p
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    localProduct, onFirst, onSecond, act A, act B, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- Multiplication by the kernel is the action of the two controlled phases
interleaved with the independent changes of basis. -/
theorem twoPhaseKernel_mulVec (H D : Matrix G G K)
    (A₀ B₀ A₁ B₁ A₂ B₂ : (G → K) ≃ₗ[K] (G → K)) (v : G × G → K) :
    (twoPhaseKernel H D A₀.toLinearMap.toMatrix' B₀.toLinearMap.toMatrix'
      A₁.toLinearMap.toMatrix' B₁.toLinearMap.toMatrix'
      A₂.toLinearMap.toMatrix' B₂.toLinearMap.toMatrix').mulVec v =
      localProduct A₂ B₂ (controlledPhase D
        (localProduct A₁ B₁ (controlledPhase H (localProduct A₀ B₀ v)))) := by
  simp only [twoPhaseKernel, ← Matrix.mulVec_mulVec, localProduct_mulVec, phaseWidthZero_mulVec]

/-- An exact two-phase weighted swap has a kernel supported on the swapped
register pairs, with its prescribed nonzero output weight on that support. -/
theorem TwoPhasesGiveWeightedSwap.exists_kernel_eq {M : Matrix G G K}
    (h : TwoPhasesGiveWeightedSwap M) :
    ∃ (A₀ B₀ A₁ B₁ A₂ B₂ : Matrix G G K) (w : G × G → Kˣ),
      twoPhaseKernel M M A₀ B₀ A₁ B₁ A₂ B₂ =
        fun x y ↦ if y.1 = x.2 ∧ y.2 = x.1 then (w x : K) else 0 := by
  obtain ⟨A₀, B₀, A₁, B₁, A₂, B₂, w, hw⟩ := h
  refine ⟨A₀.toLinearMap.toMatrix', B₀.toLinearMap.toMatrix', A₁.toLinearMap.toMatrix',
    B₁.toLinearMap.toMatrix', A₂.toLinearMap.toMatrix', B₂.toLinearMap.toMatrix', w, ?_⟩
  ext x y
  have heq := congrFun (twoPhaseKernel_mulVec M M A₀ B₀ A₁ B₁ A₂ B₂
    (Pi.single y (1 : K))) x
  rw [Matrix.mulVec_single_one, hw] at heq
  refine heq.trans ?_
  by_cases hxy : y = x.swap
  · subst y
    simp
  · have h' : ¬ (y.1 = x.2 ∧ y.2 = x.1) := by simpa [Prod.ext_iff] using hxy
    simp [h', Pi.single_eq_of_ne (Ne.symm hxy)]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
