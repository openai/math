import OAI.Computability.NearSquareRoot.PrecisionButterflyArray
import OAI.Computability.NearSquareRoot.PrecisionGridTask

/-! # The fixed-tape odd-bit butterfly with the charged short-word multiplier -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ButterflyTask

open IntegerMultiplication Code FixedPoint ProductDriver

variable {I : Type} (k : I → ℕ) (rows : (i : I) → List (Record (k i) × Record (k i)))

/-- One returning subroutine for arbitrary represented scalar and array data.
The input contains one copy of the scalar and fractional-width ruler. -/
theorem oddBitTask (c : (i : I) → Record (k i)) :
    Task (fun i => ((rows i).length+1)*GridTask.recordCost (k i))
      (query k rows c) (fun i => send (answers k rows c i)) := by
  obtain ⟨d, hd⟩ := GridTask.recordCost_scale 1200
  let R (i : I) := (d+1)*GridTask.recordCost (k i)
  have width i : k i+1 ≤ R i :=
    (GridTask.width_le_recordCost _).trans (Nat.le_mul_of_pos_left _ (by omega))
  have cost i z (hz : z ∈ cells k rows c i) : GridTask.recordCost (size z) ≤ R i := by
    have h := hd _ _ (cells_width k rows c i z hz)
    exact h.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))
  apply (runTask k rows c GridTask.adjustTask R width cost).bound (d+2)
  intro i
  dsimp [R]
  rw [Nat.mul_left_comm ((rows i).length + 1)]
  nlinarith

/-- Starting with just the payload and the address-width ruler, compute the
normalization coefficient and perform every adjacent butterfly on physical
tapes. Includes preparation, rounding both branches, and final output. -/
theorem oddBitOnTapes (hN : ∀ i, 2*(rows i).length = 2^k i) :
    TapePass (fun i => ((rows i).length+1)*GridTask.recordCost (k i))
      (fun i => ((rows i).length+1)*(k i+1))
      (rawQuery k rows) (fun i => send (answers k rows (fun i => butterflyCoefficient (k i)) i)) := by
  obtain ⟨d, hd⟩ := GridTask.recordCost_scale 1200
  let R (i : I) := (d+1)*GridTask.recordCost (k i)
  have width i : k i+1 ≤ R i :=
    (GridTask.width_le_recordCost _).trans (Nat.le_mul_of_pos_left _ (by omega))
  have h := computedOnTapes k rows GridTask.adjustTask hN R width (by
    intro i z hz
    have h := hd _ _ (cells_width k rows _ i z hz)
    exact h.trans (Nat.mul_le_mul_right _ (Nat.le_succ _)))
  apply h.scale (d+1) (2*(d+1)+1)
  · intro i; unfold R; rw [Nat.mul_left_comm]
  · intro i
    have ksmall : k i + 1 ≤ 2 ^ k i := Nat.lt_two_pow_self
    have logs := Nat.clog_le_of_le_pow (b := 2) ksmall
    have bw : GridTask.recordCost (k i) ≤ 2*(((rows i).length+1)*(k i+1)) := by
      unfold GridTask.recordCost
      have cap : k i ≤ 2*(rows i).length := by rw [hN]; omega
      nlinarith [Nat.mul_le_mul_left (k i+1) (show Nat.clog 2 (k i+1)+1 ≤ 2*((rows i).length+1) by omega)]
    have hr := Nat.mul_le_mul_left (d+1) bw
    change _ + (d+1)*GridTask.recordCost (k i) ≤ _
    nlinarith

/-- Give the tape pass an array-indexed input and output specification. -/
theorem oddBitArrayPass (m : I → ℕ) (x : (i : I) → Fin (m i) × Bool → Record (k i))
    (dim : ∀ i, 2*m i = 2^k i) :
    TapePass (fun i => (m i+1)*GridTask.recordCost (k i))
      (fun i => (m i+1)*(k i+1))
      (fun i => send (arrayWords (x i), tally (k i)))
      (fun i => send (arrayWords (arrayOutput (x i)))) := by
  have run := oddBitOnTapes k (fun i => arrayRows (x i)) (by
    intro i; simpa only [arrayRows, List.length_map, List.length_finRange] using dim i)
  rw [funext (arrayQuery_eq k m x)] at run
  simp only [arrayAnswers_eq k m x] at run
  simpa only [arrayRows, List.length_map, List.length_finRange] using run

/-- One domain for every nontrivial binary array, at every precision. -/
abbrev ArrayInput := (m : ℕ) × (Fin (2^m) × Bool → Record (m+1))

/-- The fixed machine emits the address-ordered records used by the matrix
error bound. Both complexity estimates include setup and output. -/
theorem arrayOnTapes :
    TapePass (fun a : ArrayInput => (2^a.1+1)*GridTask.recordCost (a.1+1))
      (fun a => (2^a.1+1)*(a.1+2))
      (fun a => send (arrayWords (k := a.1+1) a.2, tally (a.1+1)))
      (fun a => send (arrayWords (arrayOutput (k := a.1+1) a.2))) ∧
    ∀ a : ArrayInput, ‖recordArray (k := a.1+1) a.2‖ ≤ (2 : ℝ)^(13*(a.1+1)) →
      ‖recordArray (arrayOutput (k := a.1+1) a.2) -
        SynchronizedPadding.matrixIsometry _ (butterflyMatrix_unitary (Fin (2^a.1)))
          (recordArray (k := a.1+1) a.2)‖ ≤ 1 / (2 : ℝ)^(50*(a.1+1)) := by
  have dim (a : ArrayInput) : 2*2^a.1 = 2^(a.1+1) := by
    rw [pow_succ, Nat.mul_comm]
  constructor
  · exact oddBitArrayPass (fun a : ArrayInput => a.1+1) (fun a => 2^a.1)
      (fun a => a.2) dim
  · intro a hx
    exact arrayOutput_error _ (by omega) (dim a) hx

end ButterflyTask

end NearSquareRoot
end Computability
end OAI
