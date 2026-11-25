import OAI.LinearAlgebra.FiniteFourier.PrimeDigits
import OAI.LinearAlgebra.FiniteFourier.Upper
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # Batching active and inactive digits in a tensor-power Fourier transform -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped Kronecker

/-- Split a digit vector after its first `a` coordinates. -/
def digitSplitEquiv (ℓ a h : ℕ) :
    (Fin (a + h) → Fin ℓ) ≃ (Fin a → Fin ℓ) × (Fin h → Fin ℓ) :=
  (Fin.appendEquiv a h).symm

theorem primeTransform_add {K : Type*} [CommSemiring K] (ℓ a h : ℕ) (ζ : K) :
    primeTransform ℓ (a + h) ζ =
      (primeTransform ℓ a ζ ⊗ₖ primeTransform ℓ h ζ).submatrix
        (digitSplitEquiv ℓ a h) (digitSplitEquiv ℓ a h) := by
  ext i j
  exact Fin.prod_univ_add (fun d => ζ ^ ((i d).val * (j d).val))

/-- Apply a packed first transform along each row, padding its last batch, followed
by independent copies of the second transform on the other coordinate. -/
theorem complexity_kronecker_split_batch {K : Type*} [CommSemiring K] {I J : Type}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (A : Matrix I I K)
    (B : Matrix J J K) (W : ℕ) (hW : 0 < W) :
    complexity (A ⊗ₖ B) ≤
      (Fintype.card J ⌈/⌉ W) * complexity (Matrix.blockDiagonal (fun _ : Fin W => A)) +
      Fintype.card I * complexity B := by
  let e := (Equiv.refl I).prodCongr (Fintype.equivFin J)
  have hp := realizable_from_packed A
    (realizableAtMost_complexity (Matrix.blockDiagonal (fun _ : Fin W => A)))
    (by simpa using hW) (Fintype.card J)
  have hA : RealizableAtMost (A ⊗ₖ (1 : Matrix J J K))
      ((Fintype.card J ⌈/⌉ W) * complexity (Matrix.blockDiagonal (fun _ : Fin W => A))) := by
    rw [Matrix.kronecker_one]
    have hs := hp.submatrix e e.toEmbedding
    convert hs using 1
    · ext x y
      simp [e, Matrix.blockDiagonal_apply]
    · simp
  have hB : RealizableAtMost ((1 : Matrix I I K) ⊗ₖ B) (Fintype.card I * complexity B) := by
    rw [Matrix.one_kronecker]
    exact ((realizableAtMost_complexity B).blockDiagonal I).reindex _ _
  apply (complexity_le_iff ..).mpr
  simpa [← Matrix.mul_kronecker_mul] using hA.mul hB

/-- A circuit bound for a single digit transform from a packed transform on
the first `a` digits and unbatched transforms on the `h` remaining digits. -/
theorem primeTransform_complexity_split_batch {K : Type*} [CommSemiring K] (ℓ a h W : ℕ) (ζ : K)
    (hW : 0 < W) :
    complexity (primeTransform ℓ (a + h) ζ) ≤
      (ℓ ^ h ⌈/⌉ W) * complexity (Matrix.blockDiagonal (fun _ : Fin W => primeTransform ℓ a ζ)) +
      ℓ ^ a * complexity (primeTransform ℓ h ζ) := by
  have hp := complexity_kronecker_split_batch (primeTransform ℓ a ζ) (primeTransform ℓ h ζ) W hW
  let e := digitSplitEquiv ℓ a h
  rw [primeTransform_add]
  exact (complexity_le_iff ..).mpr (by
    simpa [e] using ((complexity_le_iff ..).mp hp).submatrix e e.toEmbedding)

/-- The classical digit-by-digit circuit bound, valid also for zero digits. -/
theorem primeTransform_classical_bound {K : Type*} [CommSemiring K] (ℓ k : ℕ) (ζ : K)
    (hℓ : 0 < ℓ) : complexity (primeTransform ℓ k ζ) ≤ (k + 1) * ℓ ^ (k + 1) := by
  have dense (n : ℕ) : complexity (primeTransform ℓ n ζ) ≤ ℓ ^ n * ℓ ^ n := by
    simpa using (complexity_le_iff _ _).mpr (realizableAtMost_card_mul_card (primeTransform ℓ n ζ))
  induction k with
  | zero =>
    have hz : complexity (primeTransform ℓ 0 ζ) ≤ 1 := by simpa using dense 0
    simpa using hz.trans hℓ
  | succ k ih =>
    have hblock : complexity (Matrix.blockDiagonal (fun _ : Fin 1 => primeTransform ℓ k ζ))
        ≤ complexity (primeTransform ℓ k ζ) := by
      simpa using (complexity_le_iff _ _).mpr
        ((realizableAtMost_complexity (primeTransform ℓ k ζ)).blockDiagonal (Fin 1))
    calc
      complexity (primeTransform ℓ (k + 1) ζ)
          ≤ ℓ * complexity (Matrix.blockDiagonal (fun _ : Fin 1 => primeTransform ℓ k ζ)) +
            ℓ ^ k * complexity (primeTransform ℓ 1 ζ) := by
              simpa using primeTransform_complexity_split_batch ℓ k 1 1 ζ (by decide)
      _ ≤ ℓ * ((k + 1) * ℓ ^ (k + 1)) + ℓ ^ k * (ℓ * ℓ) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (hblock.trans ih))
          (Nat.mul_le_mul_left _ (by simpa using dense 1))
      _ = _ := by ring

end FiniteFourier
end LinearAlgebra
end OAI
