import OAI.LinearAlgebra.FiniteFourier.GridInputs
import OAI.LinearAlgebra.FiniteFourier.CircuitParallel
import OAI.LinearAlgebra.FiniteFourier.ShearLayer

/-! # Binary gate count of a shear layer

The cost of each Boolean cube is charged to its own coordinates. Every cube dimension
is at most the logarithm of the total coordinate count, so disjoint cubes obey the
same bound as one large cube.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Finset

variable {K : Type*} [CommSemiring K] {C β : ℝ}

/-- Sum the companion cube estimate over the disjoint blocks. The total count includes even the singleton blocks. -/
private theorem sum_cube_cost_le {B I : Type} [Fintype B] [Fintype I]
    (j : B → ℕ) (e : (Σ b, Fin (j b) → Fin 2) ≃ I)
    (hC : 0 ≤ C) (hβ : 0 ≤ β) (hcube : ShearTensorBound K β C) :
    (∑ b, (complexity (gridTensor (fun _ : Fin (j b) => unitShear K)) : ℝ)) ≤
      C * (Fintype.card I : ℝ) * (1 + Real.logb 2 (Fintype.card I)) ^ β := by
  classical
  have htotal : ∑ b, 2 ^ j b = Fintype.card I := by
    simpa using Fintype.card_congr e
  have hmass : ∑ b, (2 : ℝ) ^ j b = Fintype.card I := by exact_mod_cast htotal
  have hwidth (b : B) : (j b : ℝ) ≤ Real.logb 2 (Fintype.card I) := by
    have hsize : 2 ^ j b ≤ Fintype.card I :=
      (Finset.single_le_sum (f := fun k => 2 ^ j k) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)).trans_eq htotal
    have hs : (2 : ℝ) ^ j b ≤ Fintype.card I := by exact_mod_cast hsize
    have hpow : 0 < (2 : ℝ) ^ j b := by positivity
    have hh := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num) hpow hs
    simpa [Real.logb_pow] using hh
  calc
    _ ≤ ∑ b, C * (2 : ℝ) ^ j b * (1 + Real.logb 2 (Fintype.card I)) ^ β :=
      Finset.sum_le_sum fun b _ => (hcube (j b)).trans <|
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
          (add_le_add_right (hwidth b) 1) hβ) (by positivity)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum, hmass]

/-- A shear layer obeys the companion cube estimate at its total number of registers. -/
theorem shearLayer_complexity_le {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I K}
    (hA : LayerMatrix .shear A) (hC : 0 ≤ C) (hβ : 0 ≤ β) (hcube : ShearTensorBound K β C) :
    (complexity A : ℝ) ≤ C * (Fintype.card I : ℝ) * (1 + Real.logb 2 (Fintype.card I)) ^ β := by
  obtain ⟨B, _, _, j, e, he⟩ := shearLayer_normalForm hA
  let U (b : B) := gridTensor (fun _ : Fin (j b) => unitShear K)
  have hb := RealizableAtMost.blockDiagonal' (fun b : B => realizableAtMost_complexity (U b))
  have hreindex : complexity (A.submatrix e e) = complexity A := complexity_reindex A e.symm e.symm
  have hnat : complexity A ≤ ∑ b, complexity (U b) := by
    rw [← hreindex, he]
    exact (complexity_le_iff ..).mpr hb
  exact (show (complexity A : ℝ) ≤ ∑ b, (complexity (U b) : ℝ) by exact_mod_cast hnat).trans
    (sum_cube_cost_le j e hC hβ hcube)

/-- The integral budget usable for a shear slot in a grid word. -/
theorem ShearTensorBound.realizable_layer {I : Type} [Fintype I] [DecidableEq I]
    (hcube : ShearTensorBound K β C) (hC : 0 ≤ C) (hβ : 0 ≤ β)
    {A : Matrix I I K} (hA : LayerMatrix .shear A) :
    RealizableAtMost A ⌊C * (Fintype.card I : ℝ) * (1 + Real.logb 2 (Fintype.card I)) ^ β⌋₊ :=
  (complexity_le_iff ..).mp (Nat.le_floor (shearLayer_complexity_le hA hC hβ hcube))

end FiniteFourier
end LinearAlgebra
end OAI
