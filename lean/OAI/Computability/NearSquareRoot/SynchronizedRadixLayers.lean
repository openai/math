import OAI.Computability.NearSquareRoot.SynchronizedRadix
import OAI.Computability.NearSquareRoot.SynchronizedPrimitive
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Matrix.PEquiv

/-! The normalized power-of-two Fourier axis as a word of synchronized primitive layers. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open IntegerMultiplication IntegerMultiplication.Axon Matrix SynchronizedPair

noncomputable section

private def bitReversal (k : ℕ) : Equiv.Perm (Face k) :=
  Function.Involutive.toPerm refl_ fun x => by
    funext i
    simp [refl_]

def reversalPerm (k : ℕ) : Equiv.Perm (Fin (2^k)) :=
  (localE k).symm.trans ((bitReversal k).trans (localE k))

/-- Bit-reversal permutation in the integer address order. -/
def radixReverseMatrix (k : ℕ) : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ :=
  (reversalPerm k).toPEquiv.toMatrix

/-- Exact normalized butterfly or twiddle action on the array in integer address order. -/
def radixGateMatrix (k : ℕ) (g : Radix.Gate k) : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ :=
  reindexRingEquiv ℂ (localE k) (Radix.eval 1 g)

theorem radixReverse_shortLayer (k : ℕ) : ShortLayer (radixReverseMatrix k) := by
  have hr : radixReverseMatrix k =
      (fun i j => if i = (reversalPerm k).symm j then 1 else 0) := by
    ext i j
    simp [radixReverseMatrix, PEquiv.toMatrix_apply, Equiv.eq_symm_apply]
  rw [hr]
  exact ShortLayer.permutation _

private theorem walsh_adjoint : walshᴴ = walsh := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [walsh, conjTranspose_apply]

theorem radixGate_shortLayer {k : ℕ} (g : Radix.Gate k) : ShortLayer (radixGateMatrix k g) := by
  unfold radixGateMatrix
  cases g with
  | twiddle i =>
    have hm : reindexRingEquiv ℂ (localE k) (Radix.eval 1 (.twiddle i)) =
        diagonal (fun x => frequency 1 i ((localE k).symm x)) := by
      ext x y
      change diagonal (frequency 1 i) ((localE k).symm x) ((localE k).symm y) = _
      simp [diagonal_apply]
    rw [hm]
    exact ShortLayer.phase _ fun x => Radix.frequency_unit _ _ _
  | butterfly i =>
    change ShortLayer (((SynchronizedPair.w : ℂ) • headH i).submatrix (localE k).symm (localE k).symm)
    rw [Radix.normalized_butterfly]
    exact ShortLayer.pairs (((Radix.splitBit i).symm).trans (localE k))
      (fun _ => walsh) (fun _ => walsh_threeWalsh) (fun _ => by rw [walsh_adjoint]; exact walsh_threeWalsh)

/-- Bit reversal followed in matrix product order by the explicit radix gates
gives the normalized transform. -/
theorem radix_program_eq (k : ℕ) :
    radixReverseMatrix k * ((Radix.word (layers k)).map (radixGateMatrix k)).prod =
      normalizedFourier (2 ^ k) := by
  let w := Radix.word (layers k)
  let e := reindexRingEquiv ℂ (localE k)
  have hmap : w.map (radixGateMatrix k) = (w.map (Radix.eval 1)).map e := by
    simp [List.map_map, Function.comp_def, radixGateMatrix, e]
  change radixReverseMatrix k * (w.map (radixGateMatrix k)).prod = _
  rw [hmap, ← map_list_prod]
  ext i j
  rw [radixReverseMatrix, PEquiv.toMatrix_mul_apply]
  change (w.map (Radix.eval 1)).prod ((localE k).symm (reversalPerm k i)) ((localE k).symm j) = _
  rw [show (localE k).symm (reversalPerm k i) = refl_ ((localE k).symm i) by
    simp [reversalPerm, bitReversal]; rfl]
  rw [Radix.matrix_entry, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- A complete normalized dyadic transform takes two layers per address bit,
and one permutation for bit reversal. -/
theorem radix_layers (k : ℕ) :
    ∃ word : List (Matrix (Fin (2^k)) (Fin (2^k)) ℂ),
      word.prod = normalizedFourier (2^k) ∧ (∀ M ∈ word, ShortLayer M) ∧
      word.length ≤ 2 * k + 1 := by
  refine ⟨radixReverseMatrix k :: (Radix.word (layers k)).map (radixGateMatrix k),
    radix_program_eq k, ?_, ?_⟩
  · intro M hM
    rcases List.mem_cons.mp hM with rfl | h
    · exact radixReverse_shortLayer k
    · obtain ⟨g, _, rfl⟩ := List.mem_map.mp h
      exact radixGate_shortLayer g
  · simp [Radix.word_length, layers]

end

end ShortFourier

end NearSquareRoot
end Computability
end OAI
