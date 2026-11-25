import OAI.LinearAlgebra.FiniteFourier.OccupiedWord
import OAI.LinearAlgebra.FiniteFourier.RadixWord
import OAI.LinearAlgebra.FiniteFourier.DyadicPrimeOrbit

/-! # Relabeling the occupied prime-axis word

The nonzero cyclic powers use multiplicative-orbit order, while the output
binomial basis uses frequency order. Independent row and column label changes
use one monomial slot and preserve the original contents of the workspace.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {R : Type*} [CommRing R] {I J W : Type}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W]
  {d : ℕ} {A : Matrix I I R}

/-- Relabel both sides independently, acting as the identity on the entire workspace. -/
theorem OccupiedWord.submatrixEquivs (h : OccupiedWord W d A) (rows cols : J ≃ I) :
    OccupiedWord W (d + 1) (A.submatrix rows cols) := by
  have h' := LayerWord.submatrixEquivs h (rows.sumCongr (Equiv.refl W)) (cols.sumCongr (Equiv.refl W))
  convert h' using 1
  ext (i | i) (j | j) <;> rfl

/-- The inverse coordinate change exchanges the input and output labels. -/
theorem OccupiedWord.invSubmatrixEquivs (h : OccupiedWord W d A⁻¹) (rows cols : J ≃ I) :
    OccupiedWord W (d + 1) (A.submatrix rows cols)⁻¹ := by
  rw [Matrix.inv_submatrix_equiv]
  exact h.submatrixEquivs cols rows

/-- Transport a mutually inverse pair of coordinate matrices from a common
orbit ordering to independent physical labels for the input and output. -/
theorem occupiedWord_rectangular_reindex_pair {T : Type} [Fintype T] [DecidableEq T]
    {F : Matrix I T R} {B : Matrix T I R} (hFB : F * B = 1) (orbit : I ≃ T)
    (hF : OccupiedWord W d (F.submatrix id orbit))
    (hB : OccupiedWord W d (F.submatrix id orbit)⁻¹)
    (rows : J ≃ I) (cols : J ≃ T) :
    OccupiedWord W (d + 1) (F.submatrix rows cols) ∧
    OccupiedWord W (d + 1) (B.submatrix cols rows) := by
  have hInv : (F.submatrix id orbit)⁻¹ = B.submatrix orbit id := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.submatrix_mul_equiv, hFB, Matrix.submatrix_id_id]
  rw [hInv] at hB
  let q := cols.trans orbit.symm
  constructor
  · convert hF.submatrixEquivs rows q using 2
    ext i j
    simp [Matrix.submatrix, q]
  · convert hB.submatrixEquivs q rows using 2
    ext i j
    simp [Matrix.submatrix, q]

namespace PrimeAxisOrbit

variable {p : ℕ} [Fact p.Prime] (C : PrimeAxisOrbit p)

/-- Extend the multiplicative orbit by the zero address to index the cyclic columns. -/
noncomputable def optionEquiv : Option (Fin (p-1)) ≃ ZMod p :=
  (Equiv.optionSubtype (0 : ZMod p)).symm (C.equiv.trans unitsEquivNeZero)

@[simp] theorem optionEquiv_none : C.optionEquiv none = 0 := rfl

@[simp] theorem optionEquiv_some (t : Fin (p-1)) :
    C.optionEquiv (some t) = (C.equiv t : ZMod p) := rfl

end PrimeAxisOrbit

end FiniteFourier
end LinearAlgebra
end OAI
