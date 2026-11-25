import OAI.LinearAlgebra.FiniteFourier.PrimeTemplateReindex

/-! # Free coordinate permutations around a shared query

Every endpoint may use its own chart into the same common coordinates.
The two independent charts place the appropriate entries of a single common
matrix in the block for an ordered source and target pair.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

variable {K : Type*} [CommSemiring K] {X Y : Type}

open scoped Classical in
/-- Move a source vector into the coordinates used by the common kernel. -/
def primeCommonGather (e : X ≃ Y) : Matrix Y X K :=
  (1 : Matrix Y Y K).submatrix (Equiv.refl Y) e

open scoped Classical in
/-- Read a common output vector in the coordinates of a target endpoint. -/
def primeCommonScatter (e : X ≃ Y) : Matrix X Y K :=
  (1 : Matrix Y Y K).submatrix e (Equiv.refl Y)

open scoped Classical in
private theorem primeCommonReadout {I O : Type} (g : O → I) :
    RealizableAtMost (Matrix.of fun o i => if g o = i then (1 : K) else 0) 0 := by
  classical
  refine ⟨0, le_rfl, ⟨.nil, fun o => .scaled 1 (.inl (g o))⟩, ?_⟩
  ext o i
  simp [Circuit.matrix, Circuit.eval, Readout.eval, Pi.single_apply]

/-- The gather is a zero-gate input permutation. -/
theorem primeCommonGather_free (e : X ≃ Y) : RealizableAtMost (primeCommonGather (K := K) e) 0 := by
  classical
  convert primeCommonReadout (K := K) e.symm using 1
  ext o i
  simp [primeCommonGather, Matrix.one_apply, e.symm_apply_eq]

/-- The scatter is a zero-gate output permutation. -/
theorem primeCommonScatter_free (e : X ≃ Y) : RealizableAtMost (primeCommonScatter (K := K) e) 0 := by
  classical
  convert primeCommonReadout (K := K) e using 1
  ext o i
  simp [primeCommonScatter, Matrix.one_apply]

/-- The block for two endpoints is the common matrix in the target and source charts. -/
theorem primeCommonChart_routed_factor [Fintype Y] (M : Matrix Y Y K) (outChart inChart : X ≃ Y) :
    (primeCommonScatter (K := K) outChart * M : Matrix X Y K) * primeCommonGather (K := K) inChart =
      M.submatrix outChart inChart := by
  classical
  rw [primeCommonGather, primeCommonScatter, Matrix.one_submatrix_mul, Matrix.mul_submatrix_one]
  rfl

/-- Identifying the common register set with the physical register set by any
fixed bijection gives square gathers and scatters. -/
theorem primeCommonChart_square_factor [Fintype X] (M : Matrix Y Y K) (refChart outChart inChart : X ≃ Y) :
    (primeCommonScatter (K := K) (outChart.trans refChart.symm) * M.submatrix refChart refChart :
      Matrix X X K) *
      primeCommonGather (K := K) (inChart.trans refChart.symm) = M.submatrix outChart inChart := by
  rw [primeCommonChart_routed_factor]
  ext o i
  simp [Matrix.submatrix_apply]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
