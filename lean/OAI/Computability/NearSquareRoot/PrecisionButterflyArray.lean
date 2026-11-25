import OAI.Computability.NearSquareRoot.PrecisionButterflyComputed
import OAI.Computability.NearSquareRoot.PrecisionButterflyMatrix

/-! # Address order and the numerical result of the odd-bit pass -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ButterflyTask

open IntegerMultiplication Code FixedPoint

variable {m k : ℕ}

/-- Serialize the array with the final Boolean coordinate as the low bit. -/
def arrayWords (x : Fin m × Bool → Record k) : List Dusk.Pair :=
  (List.finRange m).flatMap fun j => [Dusk.mark (x (j,false)), Dusk.mark (x (j,true))]

def arrayRows (x : Fin m × Bool → Record k) : List (Record k × Record k) :=
  (List.finRange m).map fun j => (x (j,false), x (j,true))

/-- The same two branch values as the stack command, indexed by address. -/
def arrayOutput (x : Fin m × Bool → Record k) (j : Fin m × Bool) : Record k :=
  normalizedBranch k j.2 (x (j.1,false)) (x (j.1,true)) (butterflyCoefficient k)

theorem arrayOutput_error (x : Fin m × Bool → Record k) (hk : 1 ≤ k)
    (hN : 2*m = 2^k) (hx : ‖recordArray x‖ ≤ (2 : ℝ)^(13*k)) :
    ‖recordArray (arrayOutput x) -
      SynchronizedPadding.matrixIsometry _ (butterflyMatrix_unitary (Fin m)) (recordArray x)‖ ≤
      1 / (2 : ℝ)^(50*k) := by
  apply record_butterfly_error (Fin m) hk _ x hx
  simpa [Nat.mul_comm, Fintype.card_prod] using hN.le

variable {I : Type} (k m : I → ℕ) (x : (i : I) → Fin (m i) × Bool → Record (k i))

theorem arrayQuery_eq (i : I) :
    rawQuery k (fun i => arrayRows (x i)) i = send (arrayWords (x i), tally (k i)) := by
  simp only [rawQuery, paired, PairRows.consecutive, arrayRows, arrayWords,
    List.flatMap_map]

theorem arrayAnswers_eq (i : I) :
    answers k (fun i => arrayRows (x i)) (fun i => butterflyCoefficient (k i)) i =
      arrayWords (arrayOutput (x i)) := by
  simp only [answers, arrayRows, arrayWords, arrayOutput, List.flatMap_map]

end ButterflyTask

end NearSquareRoot
end Computability
end OAI
