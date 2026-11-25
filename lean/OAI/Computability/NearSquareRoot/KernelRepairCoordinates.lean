import OAI.Computability.NearSquareRoot.KernelGeneratedRepair
import OAI.Computability.NearSquareRoot.KernelPencilDescent
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! # Rational component rows of the generated Hermite correction -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RepairCoordinates

open Matrix CyclotomicCode RepairSearch PencilDescent
open scoped CyclotomicCode

variable {R : Type*} [CommRing R] {W s a : ℕ}

private theorem gather_matrix (p : Fin W → R) (H : Matrix (Fin s) (Fin W) R) :
    gather p H = fromRows (H * diagonal p) H := by
  ext (i|i) j <;> simp [gather, Matrix.mul_diagonal]

private theorem scatter_matrix (p : Fin W → R) (H : Matrix (Fin s) (Fin W) R) :
    scatter p H = fromCols (-(diagonal p * Hᵀ)) Hᵀ := by
  ext i (j|j) <;> simp [scatter, Matrix.diagonal_mul]

private theorem discrepancy_matrix (u z : R) (p : Fin W → R) :
    discrepancy u z p =
      diagonal (fun _ => z) - (diagonal p - diagonal (fun _ => u) *
      (diagonal p * (diagonal p * diagonal p) - diagonal p)) := by
  simp only [mul_sub, diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j <;> simp [discrepancy, hij]
  ring

/-- The four quadrants of the compressed table implement the cubic residual,
expressed with ordinary matrix addition and multiplication. -/
theorem certificate_matrix (u z : R) (p : Fin W → R) (H : Matrix (Fin s) (Fin W) R)
    (t : Table R s) (ht : scatter p H * t * gather p H = discrepancy u z p) :
    let B := diagonal p
    B - diagonal (fun _ => u) * (B * (B * B) - B) -
      B * Hᵀ * (t.toBlocks₁₁ * (H * B) + t.toBlocks₁₂ * H) +
      Hᵀ * (t.toBlocks₂₁ * (H * B) + t.toBlocks₂₂ * H) = diagonal (fun _ => z) := by
  dsimp only
  rw [scatter_matrix, gather_matrix, Matrix.mul_assoc, ← fromBlocks_toBlocks t,
    fromBlocks_mul_fromRows, fromCols_mul_fromRows, discrepancy_matrix, Matrix.neg_mul] at ht
  rw [eq_sub_iff_add_eq] at ht
  rw [← ht]
  abel

private theorem diagonal_base (r : Dyadic) :
    flattenRat (diagonal (fun _ : Fin W => Number.ofBase a r)) =
      r.toRat • (1 : Matrix (Fin W × Coord a) (Fin W × Coord a) ℚ) := by
  ext ⟨i,k⟩ ⟨j,l⟩
  change (scalarBlock ((diagonal (fun _ : Fin W => Number.ofBase a r)) i j) k l).toRat = _
  by_cases hij : i = j
  · subst i
    rw [diagonal_apply_eq, scalarBlock_ofBase]
    by_cases hkl : k = l <;> simp [hkl]
  · rw [diagonal_apply_ne _ hij]
    have hz : scalarBlock (0 : Number a) k l = 0 := by
      unfold scalarBlock
      split <;> simp [show (0 : Number a).coeffs = 0 from rfl]
    simp [hz, hij]

/-- Descent of the Hermite matrix identity to arbitrarily assigned rational
ground coordinates. Every basis coefficient of every input row is independent. -/
theorem action (z : Dyadic) (p : Fin W → Number a) (H : Matrix (Fin s) (Fin W) (Number a))
    (t : Table (Number a) s)
    (ht : scatter p H * t * gather p H =
      discrepancy (Number.half a) (Number.ofBase a z) p)
    (x : Fin W × Coord a → ℚ) :
    let B := flattenRat (diagonal p)
    let G := flattenRat H
    let S := flattenRat Hᵀ
    let px := B *ᵥ x
    let pred := G *ᵥ px
    let orig := G *ᵥ x
    let u := S *ᵥ (flattenRat t.toBlocks₁₁ *ᵥ pred + flattenRat t.toBlocks₁₂ *ᵥ orig)
    let v := S *ᵥ (flattenRat t.toBlocks₂₁ *ᵥ pred + flattenRat t.toBlocks₂₂ *ᵥ orig)
    px - (1/2 : ℚ) • (B *ᵥ (B *ᵥ px) - px) - B *ᵥ u + v = z.toRat • x := by
  have he := certificate_matrix _ _ _ _ _ ht
  dsimp only at he
  have hd := congrArg flattenRat he
  simp only [flattenRat_add, flattenRat_sub, flattenRat_mul, Number.half, diagonal_base] at hd
  have hh := congrArg toRatHom (show Dyadic.ofIntWithPrec 1 1 * 2 = 1 by decide)
  simp only [map_mul, map_ofNat, map_one] at hh
  change (Dyadic.ofIntWithPrec 1 1).toRat * 2 = 1 at hh
  have hu : (Dyadic.ofIntWithPrec 1 1).toRat = 1/2 := by linarith
  have hv := Matrix.ext_iff_mulVec.mp hd x
  dsimp only
  simpa only [Matrix.add_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_sub, hu, smul_sub]
    using hv

open PencilSearch OAI.LinearAlgebra.FiniteFourier

/-- The product of all query signs, on the ground ring. -/
def baseTarget {m : ℕ} (k : Signature m) : Dyadic := ∏ j, (-1 : Dyadic) ^ (k j).val

theorem ofBase_target (a : ℕ) {m : ℕ} (k : Signature m) :
    Number.ofBase a (baseTarget k) = target a k := by
  apply (Number.ringEquiv a).injective
  change Number.value (Number.ofBase a (baseTarget k)) = (Number.ringEquiv a) (target a k)
  rw [Number.value_ofBase]
  simp only [baseTarget, target, sign, map_prod, map_pow, map_neg, map_one]

theorem baseTarget_rat {m : ℕ} (k : Signature m) :
    (baseTarget k).toRat = ∏ j, (-1 : ℚ) ^ (k j).val := by
  change toRatHom _ = _
  simp only [baseTarget, map_prod, map_pow, map_neg, map_one]

def generatedPrediction {m : ℕ} (hm : 2 ≤ m) (k : Signature m) :
    Fin (batchWidth m) → Number (batchExponent m) :=
  fun i => prediction (batchPencil m hm) k ((rowIndex m (clockDigits m) (clockPeriod m)).symm i).1

def generatedChecks (m : ℕ) :
    Matrix (Fin (batchChecks m)) (Fin (batchWidth m)) (Number (batchExponent m)) :=
  repairCheck (fun i => Number.generator (batchExponent m) ^ i.val) (batchChecks m)

theorem generated_certificate {m : ℕ} (hm : 2 ≤ m) (k : Signature m) :
    scatter (generatedPrediction hm k) (generatedChecks m) * batchTable m hm k *
        gather (generatedPrediction hm k) (generatedChecks m) =
      discrepancy (Number.half (batchExponent m)) (Number.ofBase _ (baseTarget k))
        (generatedPrediction hm k) := by
  rw [ofBase_target]
  exact table_correct (extensionExponent_nodes _ _) _ (target_sq _ k) _ _
    (badRows_card_le (batchPencil m hm) (batchPencil_good m hm) k hm)
    (good_row_value (batchPencil m hm) k)

end RepairCoordinates

end NearSquareRoot
end Computability
end OAI
