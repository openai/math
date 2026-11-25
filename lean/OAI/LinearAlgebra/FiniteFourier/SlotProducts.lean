import OAI.LinearAlgebra.FiniteFourier.SlotMatrix
import OAI.LinearAlgebra.FiniteFourier.WeightedCoefficients
import Mathlib.Data.Fintype.Sort
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # Matrix indices in tensor products of phases

Selecting some slots and their complement is one reindexing of each of the
row and column bases in the matrix of a powered array.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open scoped Classical

variable {R C K : Type*}

private def splitSlots {k : ℕ} (s : Finset (Fin k)) (A : Type*) :
    (Fin k → A) ≃ (Fin s.card → A) × (Fin sᶜ.card → A) :=
  ((finSumEquivOfFinset (s := s) rfl rfl).symm.arrowCongr (Equiv.refl A)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

/-- Interleaving two arrays gives their Kronecker product after splitting both bases. -/
theorem slotMatrix_interleaved [Mul K] {k : ℕ} (s : Finset (Fin k)) (a : (Fin s.card → R × C) → K)
    (b : (Fin sᶜ.card → R × C) → K) :
    slotMatrix (fun x ↦ a (selectSlots s x) * b (selectSlots sᶜ x)) =
      ((slotMatrix a).kronecker (slotMatrix b)).submatrix (splitSlots s R) (splitSlots s C) := rfl

private def headTail (k : ℕ) (A : Type*) : (Fin (k + 1) → A) ≃ A × (Fin k → A) where
  toFun f := (f 0, fun i ↦ f i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv _ := funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i
  right_inv _ := rfl

/-- Splitting off a single slot implements the induction for tensor powers. -/
theorem slotMatrix_power_succ [CommMonoid K] (a : R × C → K) (k : ℕ) :
    slotMatrix (slotPower a (k + 1)) =
      ((Matrix.of (fun r c ↦ a (r, c))).kronecker (slotMatrix (slotPower a k))).submatrix
         (headTail k R) (headTail k C) := by
  ext x y
  exact Fin.prod_univ_succ fun i ↦ a (x i, y i)

private def singletonSlot (A : Type*) : (Fin 1 → A) ≃ A := Equiv.funUnique _ _

/-- The first power represents the original matrix. -/
theorem slotMatrix_power_one [CommMonoid K] (a : R × C → K) :
    slotMatrix (slotPower a 1) = (Matrix.of (fun r c ↦ a (r,c))).submatrix
      (singletonSlot R) (singletonSlot C) := by
  ext x y
  simp [slotMatrix, slotPower, singletonSlot, Matrix.submatrix, Equiv.funUnique]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
