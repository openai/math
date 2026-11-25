import OAI.Computability.NearSquareRoot.PrecisionMixed
import OAI.Computability.NearSquareRoot.PrecisionGridStream
import OAI.Computability.NearSquareRoot.PrecisionProductPass

/-! # Time, visited cells and accuracy of a guarded phase application pass

The coefficient stream is supplied in lexicographic order on the wider guard
grid. The data need no conversion to that width.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section

namespace FixedPoint

open IntegerMultiplication Code

variable {I : Type} (k : I → ℕ)

abbrev PhaseAddress (i : I) := Fin (2 ^ k i)

variable (x : (i : I) → PhaseAddress k i → Record (k i))
    (c : (i : I) → PhaseAddress k i → Record (guardedK (k i)))

def phasePassQuery (i : I) : Tree :=
  send (List.ofFn (fun j => Dusk.mark (x i j)), tally (fractionBits (guardedK (k i))),
    List.ofFn (fun j => Dusk.mark (c i j)))

def phaseOutput (i : I) (j : PhaseAddress k i) : Record (k i) :=
  multiplyCoefficient (fractionBits (guardedK (k i))) (x i j) (c i j)

def phasePassReply (i : I) : Tree := send (List.ofFn fun j => Dusk.mark (phaseOutput k x c i j))

private theorem marked_bounds (i : I) (j : PhaseAddress k i) :
    size (Dusk.mark (x i j)) ≤ 800*(k i+1) ∧ size (Dusk.mark (c i j)) ≤ 800*(k i+1) ∧
      size (tally (fractionBits (guardedK (k i)))) ≤ 800*(k i+1) := by
  rw [record_size, record_size, size_tally, tally, List.length_replicate]
  unfold guardedK fractionBits
  omega

/-- The bounded command can be composed under a saved environment with the
earlier phase-prefix generator and the later transform instructions. -/
theorem phasePassBounded : Space.BoundedTask (fun i => (2^k i+1)*GridTask.recordCost (k i))
    (fun i => (2^k i+1)*(k i+1)) (phasePassQuery k x c) (phasePassReply k x c) := by
  let r i := tally (fractionBits (guardedK (k i)))
  have run := ProductPass.adjustBoundedTask (fun i => 2^k i) k r (fun i j => Dusk.mark (x i j))
    (fun i j => Dusk.mark (c i j)) 800 (fun i j => (marked_bounds k x c i j).1)
    (fun i j => (marked_bounds k x c i j).2.1)
    (fun i => (marked_bounds k x c i ⟨0, by positivity⟩).2.2)
    (fun i j => by
      dsimp only [r]
      rw [multiplyCoefficient_encoding, record_size]
      omega) (fun _ => rfl)
  unfold phasePassQuery phasePassReply
  simpa only [r, phaseOutput, multiplyCoefficient_encoding] using run

/-- A version accepting the two streams directly. A finite-state transducer
derives the guard precision from the width of the first coefficient. -/
theorem phasePassSeparate : Space.BoundedTask (fun i => (2^k i+1)*GridTask.recordCost (k i))
    (fun i => (2^k i+1)*(k i+1))
    (fun i => send (List.ofFn fun j => Dusk.mark (x i j), List.ofFn fun j => Dusk.mark (c i j)))
    (phasePassReply k x c) := by
  have run := ProductPass.adjustSeparate (fun i => 2^k i) k (fun i => guardedK (k i))
    (fun i j => Dusk.mark (x i j)) c 800 (fun i j => (marked_bounds k x c i j).1)
    (fun i j => (marked_bounds k x c i j).2.1)
    (fun i => (marked_bounds k x c i ⟨0, by positivity⟩).2.2)
    (fun i j => by rw [multiplyCoefficient_encoding, record_size]; omega) (fun _ => rfl)
  unfold phasePassReply
  simpa only [phaseOutput, multiplyCoefficient_encoding] using run

/-- A single reusable P192 command applies the entire guarded phase stream
in address order. The input includes its fractional precision once. -/
theorem phasePassTask : Task (fun i => (2^k i+1) * GridTask.recordCost (k i))
    (phasePassQuery k x c) (phasePassReply k x c) := by
  let r i := tally (fractionBits (guardedK (k i)))
  have prep := ProductPass.adjustTask (fun i => 2^k i) k r (fun i j => Dusk.mark (x i j))
    (fun i j => Dusk.mark (c i j)) 800 (fun i j => (marked_bounds k x c i j).1)
    (fun i j => (marked_bounds k x c i j).2.1)
    (fun i => (marked_bounds k x c i ⟨0, by positivity⟩).2.2)
  unfold phasePassQuery phasePassReply
  simpa only [r, phaseOutput, multiplyCoefficient_encoding] using prep

/-- A fixed physical tape machine realizes the phase pass, and the same
record array it writes satisfies the local Euclidean error tolerance. -/
theorem phasePassVerified (hpos : ∀ i, 1 ≤ k i)
    (phase : (i : I) → PhaseAddress k i → ℂ) (hu : ∀ i j, ‖phase i j‖ = 1)
    (hc : ∀ i j, ‖value _ (c i j) - phase i j‖ ≤ 1 / (2 : ℝ)^(70*k i))
    (hx : ∀ i, ‖recordArray (x i)‖ ≤ (2 : ℝ)^(13*k i)) :
    ProductDriver.TapePass (fun i => (2^k i+1)*GridTask.recordCost (k i))
      (fun i => (2^k i+1)*(k i+1)) (phasePassQuery k x c) (phasePassReply k x c) ∧
    ∀ i, ‖recordArray (phaseOutput k x c i) - phaseLayerIsometry (phase i) (hu i) (recordArray (x i))‖ ≤
      1 / (2 : ℝ)^(50*k i) := by
  constructor
  · let r i := tally (fractionBits (guardedK (k i)))
    have run := ProductPass.adjustTapePass (fun i => 2^k i) k r (fun i j => Dusk.mark (x i j))
      (fun i j => Dusk.mark (c i j)) 800 (fun i j => (marked_bounds k x c i j).1)
      (fun i j => (marked_bounds k x c i j).2.1)
      (fun i => (marked_bounds k x c i ⟨0, by positivity⟩).2.2)
      (fun i j => by
        dsimp only [r]
        rw [multiplyCoefficient_encoding, record_size]
        omega) (fun _ => rfl)
    unfold phasePassQuery phasePassReply
    simpa only [r, phaseOutput, multiplyCoefficient_encoding] using run
  · intro i
    exact applyPhase_error (hpos i) (Fintype.card_fin _) (x i) (c i) _ (hu i) (hx i) (hc i)

end FixedPoint

end

end NearSquareRoot
end Computability
end OAI
