import OAI.LinearAlgebra.FiniteFourier.GeometricMatrix
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-! # Adding a Toeplitz matrix with occupied temporary registers

Padding and truncation identify a Toeplitz matrix with a corner of a circulant.
The geometric Fourier transform diagonalizes this circulant. The four-update
identity composes additive maps while preserving arbitrary temporary values.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {K : Type*} [CommRing K]

/-- A square Toeplitz matrix is specified by its signed offset. -/
def toeplitzOfOffsets (a : ℕ) (c : ℤ → K) : Matrix (Fin a) (Fin a) K :=
  fun i j ↦ c ((i.val : ℤ) - j.val)

/-- A rectangular Toeplitz block with a signed displacement kernel. -/
def rectangularToeplitz (a e : ℕ) (c : ℤ → K) : Matrix (Fin a) (Fin e) K :=
  fun i j ↦ c ((i.val : ℤ) - j.val)

omit [CommRing K] in
/-- Embed the signed offsets as distinct residues of a cyclic convolution. -/
theorem rectangularToeplitz_eq_circulant_corner {a e b : ℕ} (hab : a+e ≤ b) (c : ℤ → K) :
    ∃ v : Fin b → K, rectangularToeplitz a e c =
      (circulant v).submatrix (Fin.castLE (by omega)) (Fin.castLE (by omega)) := by
  refine ⟨fun k ↦ if k.val < a then c k.val else c ((k.val : ℤ) - b), ?_⟩
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  change c ((i.val : ℤ) - j.val) =
    (if _ < a then c _ else c _)
  by_cases h : j.val ≤ i.val
  · rw [Fin.sub_val_of_le (show Fin.castLE (by omega : e ≤ b) j ≤ Fin.castLE (by omega) i from h)]
    simp only [Fin.val_castLE, ite_eq_left (show i.val - j.val < a by omega)]
    congr 1
    omega
  · rw [Fin.val_sub]
    simp only [Fin.val_castLE, Nat.mod_eq_of_lt (show b - j.val + i.val < b by omega),
      ite_eq_right (show ¬ b - j.val + i.val < a by omega)]
    congr 1
    omega

/-- A Toeplitz matrix factors as truncation times cyclic convolution times zero padding. -/
theorem rectangularToeplitz_eq_compressed_circulant {a e b : ℕ} (hab : a+e ≤ b) (c : ℤ → K) :
    let target := Fin.castLE (by omega : a ≤ b)
    let source := Fin.castLE (by omega : e ≤ b)
    ∃ v : Fin b → K, rectangularToeplitz a e c =
      (1 : Matrix (Fin b) (Fin b) K).submatrix target (Equiv.refl _) * circulant v *
      (1 : Matrix (Fin b) (Fin b) K).submatrix (Equiv.refl _) source := by
  dsimp only
  obtain ⟨v, hv⟩ := rectangularToeplitz_eq_circulant_corner hab c
  refine ⟨v, ?_⟩
  rw [one_submatrix_mul, mul_submatrix_one]
  exact hv

omit [CommRing K] in
/-- Embed the signed offsets as distinct residues of a cyclic convolution. -/
theorem toeplitz_eq_circulant_corner {a b : ℕ} (hab : 2*a ≤ b) (c : ℤ → K) :
    ∃ v : Fin b → K, toeplitzOfOffsets a c =
      (circulant v).submatrix (Fin.castLE (by omega)) (Fin.castLE (by omega)) :=
  rectangularToeplitz_eq_circulant_corner (by omega : a + a ≤ b) c

/-- A Toeplitz matrix factors as truncation times cyclic convolution times zero padding. -/
theorem toeplitz_eq_compressed_circulant {a b : ℕ} (hab : 2*a ≤ b) (c : ℤ → K) :
    let e := Fin.castLE (by omega : a ≤ b)
    ∃ v : Fin b → K, toeplitzOfOffsets a c =
      (1 : Matrix (Fin b) (Fin b) K).submatrix e (Equiv.refl _) * circulant v *
      (1 : Matrix (Fin b) (Fin b) K).submatrix (Equiv.refl _) e :=
  rectangularToeplitz_eq_compressed_circulant (by omega : a + a ≤ b) c

/-- A circulant becomes diagonal after changing to Fourier coordinates. -/
theorem fourier_mul_circulant_of_pow_eq_one {b : ℕ} [NeZero b] {u : K} (hu : u ^ b = 1)
    (v : Fin b → K) :
    geometricMatrix b u * circulant v =
      diagonal ((geometricMatrix b u).mulVec v) * geometricMatrix b u := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_apply,
    ← Equiv.sum_comp (Equiv.addRight j) (fun t : Fin b ↦ geometricMatrix b u i t * circulant v t j)]
  simp only [Equiv.coe_addRight, circulant_apply, add_sub_cancel_right, geometricMatrix_apply,
    Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hβ : u ^ ((k.val + j.val) % b) = u ^ (k.val + j.val) := by
    exact pow_eq_pow_of_modEq (Nat.mod_modEq _ _) hu
  rw [Fin.val_add, Nat.mul_comm i.val, pow_mul, hβ, pow_add, mul_pow,
    Nat.mul_comm i.val k.val, pow_mul, Nat.mul_comm i.val j.val, pow_mul]
  ring

theorem fourier_mul_circulant {b : ℕ} [NeZero b] {u : K} (hu : IsPrimitiveRoot u b)
    (v : Fin b → K) :
    geometricMatrix b u * circulant v =
      diagonal ((geometricMatrix b u).mulVec v) * geometricMatrix b u :=
  fourier_mul_circulant_of_pow_eq_one hu.pow_eq_one v

/-- Four additive updates implement a composite and restore the occupied
intermediate register for every initial state. -/
theorem four_updates {X Y Z : Type*} [AddCommGroup Y] [AddCommGroup Z]
    (A : X → Z) (B : Z →+ Y) (x : X) (y : Y) (z : Z) :
    let z₁ := z + A x
    let y₁ := y + B z₁
    let z₂ := z₁ - A x
    let y₂ := y₁ - B z₂
    (y₂, z₂) = (y + B (A x), z) := by
  simp
  abel

end FiniteFourier
end LinearAlgebra
end OAI
