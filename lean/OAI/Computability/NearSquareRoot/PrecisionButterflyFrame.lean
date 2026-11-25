import OAI.Computability.NearSquareRoot.PrecisionButterflyTask
import OAI.Computability.NearSquareRoot.PrecisionBoundedMap

/-! # Framed execution of the normalized odd-bit layer -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ButterflyTask

open IntegerMultiplication Code FixedPoint

variable {I : Type} (k : I → ℕ) (rows : (i : I) → List (Record (k i) × Record (k i)))

/-- A framed command retains the other callers' stacks, computes the shared
normalization coefficient, and reuses a single bounded arithmetic workspace. -/
theorem oddBitBoundedTask (dim : ∀ i, 2*(rows i).length = 2^(k i)) :
    Space.BoundedTask (fun i => ((rows i).length+1)*GridTask.recordCost (k i))
      (fun i => ((rows i).length+1)*(k i+1))
      (rawQuery k rows) (fun i => send (answers k rows (fun i => butterflyCoefficient (k i)) i)) := by
  obtain ⟨d, hd⟩ := GridTask.recordCost_scale 1200
  let c (i : I) := butterflyCoefficient (k i)
  let xs := cells k rows c
  let V := volume k rows
  let W (i : I) := (d+1)*GridTask.recordCost (k i)
  have cost (i : I) (z) (hz : z ∈ xs i) : GridTask.recordCost (size z) ≤ W i :=
    (hd _ _ (cells_width k rows c i z hz)).trans (Nat.mul_le_mul_right _ (Nat.le_succ _))
  let arg (j : (i : I) × Fin (xs i).length) := (xs j.1)[j.2.val]
  have call := (GridTask.adjustTask.on arg).mono (fun j => cost j.1 _ (List.getElem_mem _))
  have run := Space.BoundedTask.mapping xs Grid.adjust V W call (input_volume k rows c)
    (output_volume k rows c) (fun i z hz =>
      (Nat.le_succ (size z)).trans ((GridTask.width_le_recordCost _).trans (cost i z hz)))
  have full := (Space.BoundedTask.of_time (prepareComputed k rows dim)).compose run
  simp only [xs, answers_eq, cells_length] at full
  apply full.bound (8005+2*(d+1)) (8002+2*(d+1))
  · intro i
    have hwidth := GridTask.width_le_recordCost (k i)
    have hv := Nat.mul_le_mul_left ((rows i).length+1) hwidth
    change volume k rows i + (V i + 2*(rows i).length*(W i+1))+1 ≤ _
    unfold V volume W
    nlinarith
  · intro i
    let S := ((rows i).length+1)*(k i+1)
    have hq := raw_volume k rows i
    change _ ≤ 4000*S at hq
    have hk : k i+1 ≤ 2^(k i) := Nat.lt_two_pow_self
    have hlog := Nat.clog_le_of_le_pow (b := 2) hk
    have bound : GridTask.recordCost (k i) ≤ 2*S := by
      have cap : k i ≤ 2*(rows i).length := by rw [dim]; omega
      have h := Nat.mul_le_mul_left (k i+1) (show Nat.clog 2 (k i+1)+1 ≤ 2*((rows i).length+1) by omega)
      unfold GridTask.recordCost S
      nlinarith
    have hw := Nat.mul_le_mul_left (d+1) bound
    change max ((rawQuery k rows i).count + 4000*S) (4000*S + (d+1)*GridTask.recordCost (k i))+1 ≤
      (8002+2*(d+1))*(S+1)
    rcases le_total ((rawQuery k rows i).count + 4000*S)
        (4000*S + (d+1)*GridTask.recordCost (k i)) with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith

/-- Input and output are the same ordered array layout, with just the
precision ruler appended to the input. -/
theorem oddBitArrayBounded (m : I → ℕ) (x : (i : I) → Fin (m i) × Bool → Record (k i))
    (dim : ∀ i, 2*m i = 2^k i) :
    Space.BoundedTask (fun i => (m i+1)*GridTask.recordCost (k i))
      (fun i => (m i+1)*(k i+1))
      (fun i => send (arrayWords (x i), tally (k i)))
      (fun i => send (arrayWords (arrayOutput (x i)))) := by
  have h := oddBitBoundedTask k (fun i => arrayRows (x i)) (by
    intro i; simpa only [arrayRows, List.length_map, List.length_finRange] using dim i)
  rw [funext (arrayQuery_eq k m x)] at h
  simp only [arrayAnswers_eq k m x] at h
  simpa only [arrayRows, List.length_map, List.length_finRange] using h

end ButterflyTask

end NearSquareRoot
end Computability
end OAI
