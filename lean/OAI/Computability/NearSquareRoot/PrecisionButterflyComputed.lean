import OAI.Computability.NearSquareRoot.PrecisionButterflyHeader
import OAI.Computability.NearSquareRoot.PrecisionButterflyRun
import OAI.Computability.NearSquareRoot.PrecisionWalshWidth

/-! # Initializing and running a full odd-bit layer

The caller provides just the address-width ruler and the payload stream.
The program computes its normalization coefficient on the working tapes.
The setup cost is absorbed by the number of addresses in this layer.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ButterflyTask

open IntegerMultiplication Code FixedPoint ProductDriver

variable {I : Type} (k : I → ℕ) (rows : (i : I) → List (Record (k i) × Record (k i)))

def rawQuery (i : I) : Tree := send (PairRows.consecutive (paired k rows i), tally (k i))

theorem raw_volume (i : I) : (rawQuery k rows i).count ≤ volume k rows i := by
  have h := query_volume k rows (fun i => butterflyCoefficient (k i)) i
  change size (PairRows.consecutive (paired k rows i), header k (fun i => butterflyCoefficient (k i)) i) ≤ _ at h
  change size (PairRows.consecutive (paired k rows i), tally (k i)) ≤ _
  rw [size_prod] at h ⊢
  rw [header, size_prod, size_tally, tally_length, fractionBits] at h
  rw [size_tally, tally_length]
  dsimp only at h ⊢
  omega

/-- Read `k` in unary, construct both rulers and the reciprocal square-root
coefficient, and pair every branch with its arithmetic header. -/
theorem prepareComputed (hN : ∀ i, 2*(rows i).length = 2^(k i)) :
    Task (volume k rows) (rawQuery k rows)
      (fun i => send (cells k rows (fun i => butterflyCoefficient (k i)) i)) := by
  obtain ⟨d, build⟩ := buildHeader
  obtain ⟨C, hC⟩ := polynomial_le_multiple_array_length d
  have headerCmd := ((build.bound (C+1) (b' := fun n => 2^n) (by
    intro n
    refine (Nat.succ_le_succ (hC n)).trans ?_
    generalize (2 : ℕ)^n = t
    rw [Nat.succ_mul, Nat.mul_succ]
    omega)).on k)
  let c (i : I) := butterflyCoefficient (k i)
  have start := headerCmd.right (fun i => send (PairRows.consecutive (paired k rows i)))
  apply (start.compose (prepare k rows c)).bound 4
  intro i
  have hv := raw_volume k rows i
  change size (PairRows.consecutive (paired k rows i), tally (k i)) ≤ _ at hv
  rw [size_prod] at hv
  dsimp only at hv
  change size (PairRows.consecutive (paired k rows i)) + 2^k i +
    ((rows i).length+1)*(k i+1) + 1 ≤ _
  rw [← hN]
  unfold volume at *
  nlinarith

/-- The scalar is part of the computed data for all inputs to this machine. -/
theorem computedOnTapes {b : Dusk.Pair × Grid.Orb → ℕ} (call : Computes b Grid.adjust)
    (hN : ∀ i, 2*(rows i).length = 2^(k i))
    (R : I → ℕ) (hwidth : ∀ i, k i + 1 ≤ R i)
    (hcost : ∀ i z, z ∈ cells k rows (fun i => butterflyCoefficient (k i)) i → b z ≤ R i) :
    TapePass (fun i => ((rows i).length+1)*R i)
      (fun i => ((rows i).length+1)*(k i+1)+R i)
      (rawQuery k rows) (fun i => send (answers k rows (fun i => butterflyCoefficient (k i)) i)) :=
  runPreparedOnTapes k rows _ call _ (prepareComputed k rows hN) (raw_volume k rows) R hwidth hcost

end ButterflyTask

end NearSquareRoot
end Computability
end OAI
