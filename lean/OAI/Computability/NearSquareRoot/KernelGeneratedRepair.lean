import OAI.Computability.NearSquareRoot.KernelClock
import OAI.Computability.NearSquareRoot.KernelPencilAction
import OAI.Computability.NearSquareRoot.KernelRepairBatch
import OAI.LinearAlgebra.FiniteFourier.PrimeCyclotomicRepair

/-! # One generated binary pencil and correction table for all column counts

For a given query count `m` this module constructs one set of coefficients
over a fixed finite free dyadic algebra. The `4*b` stages use the same one
affine pencil. The only spectral conversions occur on the two blocks of
check rows, each of size at most the total width divided by `2*m^3`.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PencilSearch

open CyclotomicCode OAI.LinearAlgebra.FiniteFourier

def clockPeriod (m : ℕ) : ℕ := 2 ^ clockExponent m
def clockDigits (m : ℕ) : ℕ := (clockPeriod m + 1) ^ (m * 2)
def batchWidth (m : ℕ) : ℕ := rowCount m (clockDigits m) (clockPeriod m)
def batchChecks (m : ℕ) : ℕ := batchWidth m / (2*m^3)
def batchExponent (m : ℕ) : ℕ := extensionExponent (clockExponent m) (batchWidth m)

instance (m : ℕ) : NeZero (clockPeriod m) := ⟨by unfold clockPeriod; positivity⟩

theorem clockPeriod_eq (m : ℕ) : clockPeriod m = countPencilOrder 2 m := by
  simp only [clockPeriod, countPencilOrder, clockExponent_eq]

theorem batchWidth_eq (m : ℕ) : batchWidth m = primePredictorRows 2 m (countPencilOrder 2 m) := by
  simp only [batchWidth, rowCount, clockDigits, primePredictorRows, primeClockDigits, clockPeriod_eq]

theorem batchChecks_eq (m : ℕ) :
    batchChecks m = countRepairChecks 2 m (clockPeriod m ^ clockDigits m) := rfl

theorem batchExponent_eq (m : ℕ) : batchExponent m = primeRepairExtensionExponent 2 m := by
  simp only [batchExponent, extensionExponent, primeRepairExtensionExponent, batchWidth_eq,
    clockExponent_eq]

theorem two_le_batchWidth {m : ℕ} (hm : 2 ≤ m) : 2 ≤ batchWidth m := by
  have hb : 0 < clockPeriod m ^ clockDigits m := by
    unfold clockPeriod
    positivity
  have hw : 2^m ≤ 2^m * clockPeriod m ^ clockDigits m := Nat.le_mul_of_pos_right _ hb
  exact (Nat.le_self_pow (by omega : m ≠ 0) 2).trans hw

/-- All coefficients in the ordinary query pencil for the batch. -/
def batchPencil (m : ℕ) (hm : 2 ≤ m) :
    Coefficients (batchExponent m) m (clockDigits m) (clockPeriod m) :=
  generate (extensionExponent_clock _ _) (degree_le_clockPeriod m) hm

theorem batchPencil_good (m : ℕ) (hm : 2 ≤ m) : Good (batchPencil m hm) :=
  generate_good _ _ _

/-- The computed table of signed dyadic coefficient vectors at signature `k`. -/
def batchTable (m : ℕ) (hm : 2 ≤ m) (k : Signature m) :
    RepairSearch.Table (Number (batchExponent m)) (batchChecks m) :=
  correction hm (extensionExponent_nodes _ _) (batchPencil m hm) (batchPencil_good m hm) k

/-- For any number of columns and any family of operators simultaneously
diagonalized with signed eigenvalues, the generated ordinary program applies
the product to every independent input row. -/
theorem batch_correct {m : ℕ} (hm : 2 ≤ m)
    {V ν : Type*} [AddCommGroup V] [Module (Number (batchExponent m)) V]
    (S : V ≃ₗ[Number (batchExponent m)] (ν → Number (batchExponent m)))
    (sig : ν → Signature m) (Q : Fin m → Module.End (Number (batchExponent m)) V)
    (hQ : ∀ j v ω, S (Q j v) ω = sign (batchExponent m) (sig ω j) * S v ω)
    (x : Fin (batchWidth m) → V) (i : Fin (batchWidth m)) :
    let e := rowIndex m (clockDigits m) (clockPeriod m)
    let nodes := fun t : Fin (batchWidth m) => Number.generator (batchExponent m) ^ t.val
    hermiteRepairProgram 2 (Number.half (batchExponent m))
      (indexedPredictor e (batchPencil m hm) Q) S (repairCheck nodes (batchChecks m))
      ((fun k => RepairSearch.applyTable (batchTable m hm k)) ∘ sig) x i =
      S.symm ((target (batchExponent m) ∘ sig) * S (x i)) := by
  apply correction_correct (a := batchExponent m) hm (extensionExponent_nodes _ _) (batchPencil m hm) (batchPencil_good m hm)
  exact indexedPredictor_spectral _ _ (batchPencil_good m hm) S sig Q hQ

theorem batch_pencil_stages_le (m : ℕ) (hm : 2 ≤ m) :
    4 * (clockPeriod m : ℝ) ≤
      8 * (8 * Real.sqrt ((m : ℝ) * Real.log (2*m)) + 2) := by
  rw [clockPeriod_eq]
  have h := countRepair_stages_le (by decide : 2 ≤ 2) hm
  norm_num at h ⊢
  exact h

theorem batch_check_rows_le (m : ℕ) :
    2 * batchChecks m * m^3 ≤ batchWidth m := by
  have h := Nat.div_mul_le_self (batchWidth m) (2*m^3)
  simpa [batchChecks, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

end PencilSearch

end NearSquareRoot
end Computability
end OAI
