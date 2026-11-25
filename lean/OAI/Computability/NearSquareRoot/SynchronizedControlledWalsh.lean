import OAI.Computability.NearSquareRoot.SynchronizedIdleWalsh
import OAI.Computability.NearSquareRoot.SynchronizedRadixAddress
import OAI.Computability.NearSquareRoot.SynchronizedDilation

/-! # Lowering an internal radix butterfly controlled by the half bit

Each of the three Walsh rounds acts on the designated radix bit, simultaneously
in both halves. All the control is in the three diagonal tables. On the active
half these tables contain just ones and on the idle half they use fixed eighth
roots of unity selected by the value of the radix bit.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open IntegerMultiplication IntegerMultiplication.Axon SynchronizedPair Matrix

noncomputable section

variable {k : ℕ}

/-- The common unconditioned Walsh stage on an internal radix bit in both halves. -/
def bothHalvesWalsh (i : Fin k) : Matrix (Fin (2^k) ⊕ Fin (2^k)) (Fin (2^k) ⊕ Fin (2^k)) ℂ :=
  let B := radixGateMatrix k (.butterfly i)
  fromBlocks B 0 0 B

/-- Rank-indexed phase table. The second half selects the two phase constants
using the designated physical address bit. -/
def controlledPhase (i : Fin k) (a b : Fin 6) : Fin (2^k) ⊕ Fin (2^k) → ℂ :=
  Sum.elim (fun _ => 1) fun x => if rankBits x i = 0 then identityTable a else identityTable b

theorem controlledPhase_norm (i : Fin k) (a b : Fin 6) (x : Fin (2^k) ⊕ Fin (2^k)) :
    ‖controlledPhase i a b x‖ = 1 := by
  cases x <;> simp [controlledPhase, apply_ite Norm.norm, identityTable_norm]

/-- Integer numerator of the phase in eighth turns, queried using a single address bit. -/
def controlledExponent (i : Fin k) (a b : Fin 6) : Fin (2^k) ⊕ Fin (2^k) → ℤ :=
  Sum.elim (fun _ => 0) fun x => if rankBits x i = 0 then identityExponent a else identityExponent b

theorem controlledPhase_eq (i : Fin k) (a b : Fin 6) (x : Fin (2^k) ⊕ Fin (2^k)) :
    controlledPhase i a b x = Fourier.phase 8 (controlledExponent i a b x) := by
  cases x with
  | inl r => simp [controlledPhase, controlledExponent, Fourier.phase]
  | inr r =>
    dsimp only [controlledPhase, controlledExponent, Sum.elim_inr]
    split <;> exact identityTable_phase _

private def bitAddress (i : Fin k) :=
  (Radix.splitBit i).symm.trans (localE k)

private def bitMatrix (i : Fin k) (M : PairMatrix) : Matrix (Fin (2^k)) (Fin (2^k)) ℂ :=
  reindexRingEquiv ℂ (bitAddress i) (blockDiagonal fun _ => M)

private theorem bitMatrix_mul (i : Fin k) (M N : PairMatrix) :
    bitMatrix i (M*N) = bitMatrix i M * bitMatrix i N := by
  unfold bitMatrix
  rw [← map_mul, ← blockDiagonal_mul]

private theorem bitMatrix_one (i : Fin k) : bitMatrix i 1 = 1 := by
  unfold bitMatrix
  rw [show blockDiagonal (fun _ : {j : Fin k // j ≠ i} → Fin 2 => (1 : PairMatrix)) = 1
    from Matrix.blockDiagonal_one, map_one]

private theorem bitMatrix_walsh (i : Fin k) : bitMatrix i walsh = radixGateMatrix k (.butterfly i) := by
  change _ = (((w : ℂ) • headH i).submatrix (localE k).symm (localE k).symm)
  rw [Radix.normalized_butterfly]
  rfl

private theorem bitMatrix_diag (i : Fin k) (u v : ℂ) : bitMatrix i (SynchronizedPair.diag u v) =
    diagonal (fun r => if rankBits r i = 0 then u else v) := by
  have hd : SynchronizedPair.diag u v = diagonal (fun b : Fin 2 => if b = 0 then u else v) := by
    ext b c
    fin_cases b <;> fin_cases c <;> simp [SynchronizedPair.diag]
  unfold bitMatrix
  rw [hd, blockDiagonal_diagonal]
  change (diagonal (fun x : Fin 2 × ({j : Fin k // j ≠ i} → Fin 2) => if x.1 = 0 then u else v)).submatrix
    (bitAddress i).symm (bitAddress i).symm = _
  rw [Matrix.submatrix_diagonal_equiv]
  congr 1
  funext r
  rw [rankBits_eq]
  rfl

/-- The three common Walsh rounds with their actual scalar tables implement the
controlled butterfly, restoring every entry of the idle half exactly. -/
theorem firstHalf_butterfly_threeWalsh (i : Fin k) :
    firstHalf (radixGateMatrix k (.butterfly i)) =
      bothHalvesWalsh i * diagonal (controlledPhase i 0 1) * bothHalvesWalsh i *
      diagonal (controlledPhase i 2 3) * bothHalvesWalsh i * diagonal (controlledPhase i 4 5) := by
  let B := radixGateMatrix k (.butterfly i)
  have hB : bitMatrix i walsh = B := bitMatrix_walsh i
  have hsq : B * B = 1 := by rw [← hB, ← bitMatrix_mul, walsh_sq, bitMatrix_one]
  let t (a b : Fin 6) := Matrix.diagonal (fun r => if rankBits r i = 0 then identityTable a else identityTable b)
  have hid := congrArg (bitMatrix i) identityTable_word
  simp only [bitMatrix_one, bitMatrix_mul, hB, bitMatrix_diag] at hid
  have hd (a b : Fin 6) : diagonal (controlledPhase i a b) = fromBlocks 1 0 0 (t a b) := by
    rw [show (1 : Matrix (Fin (2^k)) (Fin (2^k)) ℂ) = diagonal (fun _ => 1) from Matrix.diagonal_one.symm,
      Matrix.fromBlocks_diagonal]
    rfl
  change fromBlocks B 0 0 1 = _
  simp only [hd, bothHalvesWalsh, fromBlocks_multiply, mul_zero, zero_mul, zero_add, add_zero,
    mul_one]
  change fromBlocks B 0 0 1 = fromBlocks (B * B * B) 0 0 _
  rw [hsq, one_mul]
  exact congrArg (fromBlocks B 0 0) hid

end
end ShortFourier

end NearSquareRoot
end Computability
end OAI
