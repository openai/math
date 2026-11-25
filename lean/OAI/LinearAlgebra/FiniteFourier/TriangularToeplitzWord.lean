import OAI.LinearAlgebra.FiniteFourier.BorrowedComposition
import OAI.LinearAlgebra.FiniteFourier.DiagonalShear
import OAI.LinearAlgebra.FiniteFourier.GeometricNewton
import OAI.LinearAlgebra.FiniteFourier.OccupiedWord
import OAI.LinearAlgebra.FiniteFourier.ToeplitzCirculant
import OAI.LinearAlgebra.FiniteFourier.ToeplitzWorkspace

/-! # From additive Toeplitz operations to triangular Toeplitz factors

The commutator returns the partner array and every temporary register. The
bound on the number of slot pairs is uniform in the matrix size and field.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open Matrix ExactFourier.CoefficientTime

variable {K : Type*} [CommRing K] {W I : Type} [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]

private theorem additiveWord_upper {d : ℕ} {S : Matrix I I K} (h : AdditiveWord W d S) :
    OccupiedWord W d (fromBlocks 1 S 0 1) := by
  have h' := OccupiedWord.relabel h (Equiv.sumComm I I)
  convert h' using 1
  ext (i|i) (j|j) <;> rfl

private theorem occupiedWord_pair {d : ℕ} {S T : Matrix I I K}
    (hST : S*T = 1) (hTS : T*S = 1) (hS : AdditiveWord W d S) (hT : AdditiveWord W d (-T)) :
    OccupiedWord W (3*d+1) (fromBlocks S 0 0 T) := by
  rw [← paired_toeplitz_factorization S T hST hTS, show 3*d+1 = d+d+d+1 by omega]
  exact (((additiveWord_upper hS).mul hT).mul (additiveWord_upper hS)).mul
    (LayerWord.occupied layerWord_signedSwap)

private def seriesOffsets (f : PowerSeries K) (k : ℤ) : K :=
  if 0 ≤ k then PowerSeries.coeff k.toNat f else 0

private theorem trunc_eq_toeplitz (a : ℕ) (f : PowerSeries K) :
    truncMatrix a f = toeplitzOfOffsets a (seriesOffsets f) := by
  ext i j
  by_cases hi : j.val ≤ i.val
  · have he : ((i.val : ℤ) - j.val).toNat = i.val - j.val := by omega
    simp [truncMatrix, toeplitzOfOffsets, seriesOffsets, hi, he]
  · simp [truncMatrix, toeplitzOfOffsets, seriesOffsets, hi]

/-- A unitriangular Toeplitz factor acts on one occupied array, restoring
its partner array and the workspace of the additive Toeplitz updates. -/
theorem lowerUnitToeplitz_word_of_units {a d : ℕ} (u : Kˣ)
    (hu : ∀ i, 0 < i → i < a → IsUnit ((u : K)^i - 1))
    (hadd : ∀ c : ℤ → K, AdditiveWord W d (toeplitzOfOffsets a c))
    {h : PowerSeries K} (hh : h.constantCoeff = 1) :
    OccupiedWord (Fin a ⊕ W) (6*d+4) (truncMatrix a h) := by
  obtain ⟨f, hc⟩ := toeplitz_commutator_units u hu h hh
  let S := truncMatrix a (f : PowerSeries K)
  let T := truncMatrix a (↑f⁻¹ : PowerSeries K)
  have hST : S*T=1 := by simp [S, T, ← truncMatrix_mul]
  have hTS : T*S=1 := by simp [S, T, ← truncMatrix_mul]
  have hpos (g : PowerSeries K) : AdditiveWord W d (truncMatrix a g) := by
    rw [trunc_eq_toeplitz]
    apply hadd
  have hneg (g : PowerSeries K) : AdditiveWord W d (-(truncMatrix a g)) := by
    rw [trunc_eq_toeplitz]
    exact hadd (fun k ↦ -seriesOffsets g k)
  have hB := occupiedWord_pair hST hTS (hpos _) (hneg _)
  have hB' := occupiedWord_pair hTS hST (hpos _) (hneg _)
  have hdi (v : Kˣ) : OccupiedWord W 1
      (fromBlocks (scalingDiagonal a (v : K)) 0 0 (1 : Matrix (Fin a) (Fin a) K)) :=
    (layerWord_parallel (layerWord_of_layer (layerMatrix_diagonal_units
      (fun i : Fin a ↦ v.isUnit.pow i.val))) (layerWord_one (I := Fin a) (K := K) 1)).occupied
  let D := scalingDiagonal a (u : K)
  let D' := scalingDiagonal a (↑u⁻¹ : K)
  have hword : OccupiedWord W (1+(3*d+1)+1+(3*d+1))
      (fromBlocks D 0 0 (1 : Matrix (Fin a) (Fin a) K) * fromBlocks S 0 0 T *
       fromBlocks D' 0 0 1 * fromBlocks T 0 0 S) :=
    (((hdi u).mul hB).mul (hdi u⁻¹)).mul hB'
  rw [paired_commutator D D' S T hTS, show 1+(3*d+1)+1+(3*d+1) = 6*d+4 by omega] at hword
  rw [hc]
  exact OccupiedWord.assoc hword

private theorem lowerToeplitz_word {K : Type*} [Field K] {a b d : ℕ} (ha : 0 < a) (hab : a ≤ b) {u : K}
    (hu : IsPrimitiveRoot u b) (hadd : ∀ c : ℤ → K, AdditiveWord W d (toeplitzOfOffsets a c))
    {f : PowerSeries K} (hf : f.constantCoeff ≠ 0) :
    OccupiedWord (Fin a ⊕ W) (6*d+5) (truncMatrix a f) := by
  let g := PowerSeries.C (f.constantCoeff)⁻¹ * f
  have hg : g.constantCoeff = 1 := by simp [g, hf]
  have h := lowerUnitToeplitz_word_of_units (hu.isUnit (ha.trans_le hab).ne').unit
    (fun i hi hi' => by
      simpa only [IsUnit.unit_spec] using isUnit_iff_ne_zero.mpr
        (sub_ne_zero.mpr (hu.pow_ne_one_of_pos_of_lt hi.ne' (hi'.trans_le hab)))) hadd hg
  have hd : LayerWord 1 (diagonal (fun _ : Fin a ↦ f.constantCoeff)) :=
    layerWord_of_layer (layerMatrix_diagonal (fun _ ↦ hf))
  have heq : truncMatrix a f = diagonal (fun _ : Fin a ↦ f.constantCoeff) * truncMatrix a g := by
    ext i j
    rw [diagonal_mul]
    by_cases hij : j.val ≤ i.val <;> simp [truncMatrix, g, hij, PowerSeries.coeff_C_mul, hf]
  rw [heq, show 6*d+5 = 1+(6*d+4) by omega]
  exact hd.occupied.mul h

/-- Diagonals and lower or upper triangular Toeplitz factors all have depth
at most `6d+5` when an additive Toeplitz update has depth `d`. -/
theorem gridFactor_word_of_additive {K : Type*} [Field K] {a b d : ℕ} (ha : 0 < a) (hab : a ≤ b) {u : K}
    (hu : IsPrimitiveRoot u b) (hadd : ∀ c : ℤ → K, AdditiveWord W d (toeplitzOfOffsets a c))
    {A : Matrix (Fin a) (Fin a) K} (hA : IsGridDiagonalOrToeplitz A) :
    OccupiedWord (Fin a ⊕ W) (6*d+5) A := by
  cases hA with
  | diagonal v hv =>
    exact LayerWord.pad (by omega) ((layerWord_of_layer (layerMatrix_diagonal hv)).occupied)
  | lower f hf => exact lowerToeplitz_word ha hab hu hadd hf
  | upper f hf =>
    have he : (truncMatrix a f)ᵀ = (truncMatrix a f).submatrix
        (Fin.revPerm (n := a)).symm (Fin.revPerm (n := a)).symm := by
      ext i j
      change (if i.val ≤ j.val then PowerSeries.coeff (j.val-i.val) f else 0) =
        (if a-(j.val+1) ≤ a-(i.val+1) then PowerSeries.coeff (a-(i.val+1)-(a-(j.val+1))) f else 0)
      have hi := i.isLt
      have hj := j.isLt
      have h₁ : a - (i.val + 1) + (i.val + 1) = a := Nat.sub_add_cancel (by omega)
      have h₂ : a - (j.val + 1) + (j.val + 1) = a := Nat.sub_add_cancel (by omega)
      by_cases hij : i.val ≤ j.val
      · rw [ite_eq_left hij, ite_eq_left (by omega : a-(j.val+1) ≤ a-(i.val+1))]
        rw [show a-(i.val+1)-(a-(j.val+1)) = j.val-i.val by omega]
      · rw [ite_eq_right hij, ite_eq_right (by omega : ¬ a-(j.val+1) ≤ a-(i.val+1))]
    rw [he]
    exact OccupiedWord.relabel (lowerToeplitz_word ha hab hu hadd hf) Fin.revPerm

end

end

end FiniteFourier
end LinearAlgebra
end OAI
