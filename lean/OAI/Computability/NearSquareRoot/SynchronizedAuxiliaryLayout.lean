import OAI.Computability.NearSquareRoot.SynchronizedBorrowedPass
import OAI.Computability.NearSquareRoot.SynchronizedShortTransform

/-! # Layout of a restored Fourier batch

Bluestein's dilation has two halves of length `r`. The batch placement uses a
primary fiber of size `a` and a separate list of borrowed slots. Both layouts
assign the same underlying flat indices to the occupied coordinates.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix SynchronizedBorrowing
noncomputable section

/-- Relabel the two Fourier halves as one list of active and borrowed slots. -/
def auxiliaryLayout {a r : ℕ} (har : a ≤ r) :
    Fin r ⊕ Fin r ≃ Fin a ⊕ Fin (2*r-a) :=
  finSumFinEquiv.trans ((finCongr (by omega)).trans finSumFinEquiv.symm)

theorem auxiliaryLayout_inl {a r : ℕ} (har : a ≤ r) (j : Fin a) :
    auxiliaryLayout har (Sum.inl (Fin.castLE har j)) = Sum.inl j := by
  apply finSumFinEquiv.injective
  simp [auxiliaryLayout, Fin.ext_iff]

private theorem activeFiber_entry {a r : ℕ} (har : a ≤ r) (i : Fin r ⊕ Fin r) (j : Fin a) :
    activeFiber har i j = if i = Sum.inl (Fin.castLE har j) then 1 else 0 := by
  cases i <;> simp [activeFiber, firstHalfInclusion, firstCoords]

private theorem rowInclusion_entry {a c : ℕ} (i : Fin a ⊕ Fin c) (j : Fin a) :
    rowInclusion a c i j = if i = Sum.inl j then 1 else 0 := by
  cases i <;> simp [rowInclusion, Matrix.one_apply]

theorem auxiliaryLayout_inclusion {a r : ℕ} (har : a ≤ r) :
    (activeFiber har).submatrix (auxiliaryLayout har).symm id = rowInclusion a (2*r-a) := by
  ext i j
  simp only [submatrix_apply, id_eq, activeFiber_entry, rowInclusion_entry]
  simp only [Equiv.symm_apply_eq, auxiliaryLayout_inl]

private theorem extend_submatrix {X Y A : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype A] [DecidableEq A]
    (E : Matrix X A ℂ) (U : Matrix A A ℂ) (f : Y ≃ X) :
    (extend E U).submatrix f f = extend (E.submatrix f id) U := by
  ext i j
  simp only [extend, submatrix_apply, Matrix.add_apply, Matrix.one_apply, Equiv.apply_eq_iff_eq,
    Matrix.mul_apply, Matrix.conjTranspose_apply, id_eq]

/-- In the batch layout the explicit restored short-transform circuit is the
occupied matrix with an exact identity block on the borrowed slots. -/
theorem auxiliaryLayout_extend {a r : ℕ} (har : a ≤ r) (U : Matrix (Fin a) (Fin a) ℂ) :
    (extend (activeFiber har) U).submatrix (auxiliaryLayout har).symm (auxiliaryLayout har).symm =
      extend (rowInclusion a (2*r-a)) U := by
  rw [extend_submatrix, auxiliaryLayout_inclusion]

theorem auxiliaryLayout_restored {a r : ℕ} [NeZero a] [NeZero r]
    (har : a ≤ r) (hwrap : 2*a-1 ≤ r) :
    (restoredShortTransform har).submatrix (auxiliaryLayout har).symm (auxiliaryLayout har).symm =
      fromBlocks (normalizedFourier a) 0 0 1 := by
  rw [restoredShortTransform_eq hwrap, auxiliaryLayout_extend, extend_rowInclusion]

end
end ShortFourier

end NearSquareRoot
end Computability
end OAI
