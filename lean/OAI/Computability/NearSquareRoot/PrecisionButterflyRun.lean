import OAI.Computability.NearSquareRoot.PrecisionButterflyPrepare
import OAI.Computability.NearSquareRoot.PrecisionProductRelease

/-! # Running the rounded direct butterfly on adjacent tape records

The common scalar and binary-point ruler are supplied once. The pass emits
the two normalized branches consecutively, in address order. Scratch for a
single record operation can be reused after each pair of operands is consumed.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ButterflyTask

open IntegerMultiplication Code FixedPoint ProductDriver

variable {I : Type} (k : I → ℕ) (rows : (i : I) → List (Record (k i) × Record (k i)))
    (c : (i : I) → Record (k i))

def query (i : I) : Tree := send (PairRows.consecutive (paired k rows i), header k c i)

def answers (i : I) : List Dusk.Pair :=
  (rows i).flatMap fun p => [Dusk.mark (normalizedBranch (k i) false p.1 p.2 (c i)),
                             Dusk.mark (normalizedBranch (k i) true p.1 p.2 (c i))]

theorem answers_eq (i : I) : (cells k rows c i).map Grid.adjust = answers k rows c i := by
  simp only [cells, List.map_map, branches, answers, header]
  induction rows i with
  | nil => rfl
  | cons p l ih => simp [Function.comp_def, multiply_encoding, normalizedBranch] at ih ⊢; exact ih

private theorem list_size_le {A : Type*} [Codec A] {w : ℕ} {l : List A}
    (h : ∀ a ∈ l, size a ≤ w) : size l ≤ l.length*(w+1)+1 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    have hh := h x List.mem_cons_self
    simp only [size_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem output_width (i : I) {z : Dusk.Pair × Grid.Orb} (hz : z ∈ cells k rows c i) :
    size (Grid.adjust z) = 384 * k i + 23 := by
  obtain ⟨_, h, rfl⟩ := List.mem_map.mp hz
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp h
  exact (congrArg size (multiply_encoding (k i) x (c i))).trans (record_size _ _)

/-- A common envelope for the encoded streams at the arithmetic call boundaries. -/
def volume (i : I) := 4000 * (((rows i).length+1)*(k i+1))

theorem query_volume (i : I) : (query k rows c i).count ≤ volume k rows i := by
  change size (PairRows.consecutive (paired k rows i), header k c i) ≤ _
  rw [size_prod, PairRows.size_consecutive]
  have hp : size (paired k rows i) ≤ (rows i).length*((384*k i+23)*2+2)+1 := by
    convert list_size_le (l := paired k rows i) (w := (384*k i+23)*2+1) ?_ using 1
    · simp [paired]
    · intro a h
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp h
      rw [size_prod, record_size, record_size]
      omega
  rw [header, size_prod, record_size, size_tally, tally_length, fractionBits]
  unfold volume
  nlinarith

theorem input_volume (i : I) : size (cells k rows c i) ≤ volume k rows i := by
  have h := list_size_le (cells_width k rows c i)
  rw [cells_length] at h
  unfold volume
  nlinarith

theorem output_volume (i : I) : size ((cells k rows c i).map Grid.adjust) ≤ volume k rows i := by
  have h := list_size_le (l := (cells k rows c i).map Grid.adjust) (w := 384*k i+23) (by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact (output_width k rows c i hz).le)
  rw [List.length_map, cells_length] at h
  unfold volume
  nlinarith

/-- The same pass as a returning stack command for use inside a composition. -/
theorem runTask {b : Dusk.Pair × Grid.Orb → ℕ} (call : Computes b Grid.adjust)
    (R : I → ℕ) (hwidth : ∀ i, k i + 1 ≤ R i)
    (hcost : ∀ i z, z ∈ cells k rows c i → b z ≤ R i) :
    Task (fun i => ((rows i).length+1)*R i)
      (query k rows c) (fun i => send (answers k rows c i)) := by
  have run := (prepare k rows c).compose (call.mapping.on (cells k rows c))
  simp only [answers_eq] at run
  apply run.bound 4005
  intro i
  have total := costSum_le (u := fun _ => R i) (hcost i)
  simp only [costSum, List.map_const', List.sum_replicate, nsmul_eq_mul, Nat.cast_id,
    cells_length] at total
  have hw := Nat.mul_le_mul_left ((rows i).length+1) (hwidth i)
  have hv := input_volume k rows c i
  change ((rows i).length+1)*(k i+1) +
    (size (cells k rows c i) + ((cells k rows c i).map b).sum) + 1 ≤ _
  unfold volume at hv
  nlinarith

/-- Charge a record computation with clock `b` against a common single-call
budget `R`. The factor `R` occurs once in the space bound for the full pass. -/
theorem runPreparedOnTapes {b : Dusk.Pair × Grid.Orb → ℕ} (call : Computes b Grid.adjust)
    (q : I → Tree) (prep : Task (volume k rows) q (fun i => send (cells k rows c i)))
    (hq : ∀ i, (q i).count ≤ volume k rows i)
    (R : I → ℕ) (hwidth : ∀ i, k i + 1 ≤ R i)
    (hcost : ∀ i z, z ∈ cells k rows c i → b z ≤ R i) :
    TapePass (fun i => ((rows i).length+1)*R i)
      (fun i => ((rows i).length+1)*(k i+1)+R i)
      q (fun i => send (answers k rows c i)) := by
  let W i := 400*R i
  have step i z (hz : z ∈ cells k rows c i) : b z + size (Grid.adjust z) + 1 ≤ W i := by
    rw [output_width k rows c i hz]
    dsimp [W]
    have := hwidth i
    have := hcost i z hz
    omega
  have h := mapOnTapes call prep hq (input_volume k rows c)
    (output_volume k rows c) step
  simp only [answers_eq] at h
  apply h.scale 5000 5000
  · intro i
    rw [cells_length]
    have hw := Nat.mul_le_mul_left ((rows i).length+1) (hwidth i)
    have hpos : 1 ≤ R i := by have := hwidth i; omega
    dsimp [volume, W]
    nlinarith
  · intro i
    have hpos : 1 ≤ R i := by have := hwidth i; omega
    dsimp [volume, W]
    nlinarith

/-- Physical pass when the scalar setup header has already been computed. -/
theorem runOnTapes {b : Dusk.Pair × Grid.Orb → ℕ} (call : Computes b Grid.adjust)
    (R : I → ℕ) (hwidth : ∀ i, k i + 1 ≤ R i)
    (hcost : ∀ i z, z ∈ cells k rows c i → b z ≤ R i) :
    TapePass (fun i => ((rows i).length+1)*R i)
      (fun i => ((rows i).length+1)*(k i+1)+R i)
      (query k rows c) (fun i => send (answers k rows c i)) :=
  runPreparedOnTapes k rows c call _ ((prepare k rows c).mono fun i => by
    unfold volume; omega) (query_volume k rows c) R hwidth hcost

end ButterflyTask

end NearSquareRoot
end Computability
end OAI
