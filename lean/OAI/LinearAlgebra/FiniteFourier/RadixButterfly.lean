import OAI.LinearAlgebra.FiniteFourier.RadixWord
import OAI.LinearAlgebra.FiniteFourier.TransvectionLayer
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # The two radix butterflies

The Fourier transforms on two and three coordinates factor into, respectively, two
and six transvections around an explicit diagonal. The identities even hold for
geometric evaluation at an arbitrary element of a commutative ring.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {K : Type*}

section Ring

variable [CommRing K]

/-- Pivots for the two-coordinate transform. -/
def radixTwoDiagonal (q : K) : Fin 2 → K := ![1, q - 1]

/-- Pivots for the three-coordinate transform. -/
def radixThreeDiagonal (q : K) : Fin 3 → K :=
  ![1, q - 1, (q ^ 2 - 1) * (q ^ 2 - q)]

theorem geometricMatrix_two_transvections (q : K) :
    geometricMatrix 2 q =
      transvection 1 0 1 * diagonal (radixTwoDiagonal q) * transvection 0 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [geometricMatrix_apply, radixTwoDiagonal, Matrix.diagonal_apply] <;>
    norm_num [transvection, Matrix.one_apply, Matrix.single_apply]

theorem geometricMatrix_three_transvections (q : K) :
    geometricMatrix 3 q =
      transvection 1 0 1 * (transvection 2 0 1 * (transvection 2 1 (1 + q) *
      diagonal (radixThreeDiagonal q))) *
      transvection 1 2 (1 + q) * transvection 0 2 1 * transvection 0 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [geometricMatrix_apply, radixThreeDiagonal, Matrix.diagonal_apply] <;>
    norm_num [transvection, Matrix.one_apply, Matrix.single_apply] <;> ring

private theorem unitTransvectionWord {n : ℕ} (a b : Fin n) (h : a ≠ b) :
    LayerWord 1 (transvection a b (1 : K)) :=
  layerWord_of_layer (LayerMatrix.unitTransvection h)

/-- A two-point evaluation butterfly needs one diagonal pivot, the difference of its nodes. -/
theorem layerWord_radixTwo_of_separated {q : K}
    (hsep : Pairwise fun i j : Fin 2 => IsUnit (q ^ i.val - q ^ j.val)) :
    LayerWord 3 (geometricMatrix 2 q) := by
  have h₁ : IsUnit (q - 1) := by
    simpa using hsep (show (1 : Fin 2) ≠ 0 by decide)
  have hD : ∀ i, IsUnit (radixTwoDiagonal q i) := by
    intro i
    fin_cases i <;> simp [radixTwoDiagonal, h₁]
  rw [geometricMatrix_two_transvections]
  exact layerWord_mul (layerWord_mul (unitTransvectionWord 1 0 (by decide))
    (layerWord_of_layer (layerMatrix_diagonal_units hD))) (unitTransvectionWord 0 1 (by decide))

/-- Unit separation makes both the three-point pivots and the multiplier `1 + q` units. -/
theorem layerWord_radixThree_of_separated {q : K}
    (hsep : Pairwise fun i j : Fin 3 => IsUnit (q ^ i.val - q ^ j.val)) :
    LayerWord 11 (geometricMatrix 3 q) := by
  have h₁ : IsUnit (q - 1) := by
    simpa using hsep (show (1 : Fin 3) ≠ 0 by decide)
  have h₂ : IsUnit (q ^ 2 - 1) := by
    simpa using hsep (show (2 : Fin 3) ≠ 0 by decide)
  have h₃ : IsUnit (q ^ 2 - q) := by
    simpa using hsep (show (2 : Fin 3) ≠ 1 by decide)
  have hsum : IsUnit (1 + q) := by
    apply isUnit_of_mul_isUnit_left (y := q - 1)
    rwa [show (1 + q) * (q - 1) = q ^ 2 - 1 by ring]
  have hD : ∀ i, IsUnit (radixThreeDiagonal q i) := by
    intro i
    fin_cases i <;> simp [radixThreeDiagonal, h₁, h₂, h₃]
  rw [geometricMatrix_three_transvections]
  have hL := layerWord_mul (unitTransvectionWord (1 : Fin 3) 0 (by decide))
    (layerWord_mul (unitTransvectionWord (2 : Fin 3) 0 (by decide))
      (layerWord_mul (layerWord_transvection_unit (i := (2 : Fin 3)) (j := 1) (by decide) hsum.unit)
        (layerWord_of_layer (layerMatrix_diagonal_units hD))))
  exact layerWord_mul (layerWord_mul (layerWord_mul hL
    (layerWord_transvection_unit (i := (1 : Fin 3)) (j := 2) (by decide) hsum.unit))
    (unitTransvectionWord 0 2 (by decide))) (unitTransvectionWord 0 1 (by decide))

/-- Each radix-power stage costs at most thirteen synchronized pairs over a
commutative ring containing a unit-separated root of unity. -/
theorem layerWord_smallRadixPow_of_separated {r : ℕ} (hr : r = 2 ∨ r = 3) (j : ℕ) {q : K}
    (hpow : q ^ (r ^ j) = 1)
    (hsep : Pairwise fun i k : Fin (r ^ j) => IsUnit (q ^ i.val - q ^ k.val)) :
    LayerWord (13 * j) (geometricMatrix (r ^ j) q) := by
  apply layerWord_geometricMatrix_radixPow_of_separated (C := 11)
    (by rcases hr with rfl | rfl <;> decide) _ j hpow hsep
  intro ζ _ hζ
  rcases hr with rfl | rfl
  · exact (layerWord_radixTwo_of_separated hζ).pad (by decide)
  · exact layerWord_radixThree_of_separated hζ

end Ring

variable [Field K]

theorem radixTwoDiagonal_ne_zero {q : K} (h : IsPrimitiveRoot q 2) (i : Fin 2) :
    radixTwoDiagonal q i ≠ 0 := by
  have hq := h.ne_one (by decide)
  fin_cases i <;> simp [radixTwoDiagonal, sub_ne_zero, hq]

theorem radixThreeDiagonal_ne_zero {q : K} (h : IsPrimitiveRoot q 3) (i : Fin 3) :
    radixThreeDiagonal q i ≠ 0 := by
  have hq := h.ne_one (by decide)
  have h₀ : q ^ 2 ≠ q ^ 0 := fun e => by
    have := h.pow_inj (by decide : 2 < 3) (by decide : 0 < 3) e
    omega
  have h₁ : q ^ 2 ≠ q ^ 1 := fun e => by
    have := h.pow_inj (by decide : 2 < 3) (by decide : 1 < 3) e
    omega
  simp only [pow_zero, pow_one] at h₀ h₁
  fin_cases i <;> simp [radixThreeDiagonal, sub_ne_zero, hq, h₀, h₁]

private theorem primitiveRoot_separated {q : K} {n : ℕ} (hq : IsPrimitiveRoot q n) :
    Pairwise fun i j : Fin n => IsUnit (q ^ i.val - q ^ j.val) :=
  fun i j hij => isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr
    (fun h => hij (Fin.ext (hq.pow_inj i.isLt j.isLt h))))

theorem layerWord_radixTwo {q : K} (hq : IsPrimitiveRoot q 2) :
    LayerWord 3 (geometricMatrix 2 q) :=
  layerWord_radixTwo_of_separated (primitiveRoot_separated hq)

theorem layerWord_radixThree {q : K} (hq : IsPrimitiveRoot q 3) :
    LayerWord 11 (geometricMatrix 3 q) :=
  layerWord_radixThree_of_separated (primitiveRoot_separated hq)

/-- Over every field admitting a primitive root, Fourier transforms of length
`2 ^ j` and `3 ^ j` take at most `13 * j` synchronized layer pairs. -/
theorem layerWord_smallRadixPow {r : ℕ} (hr : r = 2 ∨ r = 3) (j : ℕ) {q : K}
    (hq : IsPrimitiveRoot q (r ^ j)) : LayerWord (13 * j) (geometricMatrix (r ^ j) q) :=
  layerWord_smallRadixPow_of_separated hr j hq.pow_eq_one (primitiveRoot_separated hq)

end FiniteFourier
end LinearAlgebra
end OAI
