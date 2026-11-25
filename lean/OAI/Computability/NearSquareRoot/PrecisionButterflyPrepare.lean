import OAI.Computability.NearSquareRoot.PrecisionButterfly
import OAI.Computability.NearSquareRoot.PrecisionCartesian
import OAI.Computability.NearSquareRoot.PrecisionPairRows

/-! # Preparing fixed-point records for a normalized butterfly

The input stream alternates the two operands of each butterfly. The program
packs the pairs, computes both signed branches, and broadcasts the supplied
scale and fractional-bit ruler to every output record.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ButterflyTask

open IntegerMultiplication IntegerMultiplication.Code FixedPoint

variable {I : Type*} (k : I → ℕ)
    (rows : (i : I) → List (Record (k i) × Record (k i)))
    (c : (i : I) → Record (k i))

/-- Packed input pairs of tape words, before arithmetic. -/
def paired (i : I) : List (Dusk.Pair × Dusk.Pair) :=
  (rows i).map fun p => (Dusk.mark p.1, Dusk.mark p.2)

/-- The sum and difference records in butterfly output order. -/
def branches (i : I) : List (Record (k i)) :=
  (rows i).flatMap fun p => [butterflySum false p.1 p.2, butterflySum true p.1 p.2]

/-- The ruler and encoded common scale of the butterfly. -/
def header (i : I) : Grid.Orb := (tally (fractionBits (k i)), Dusk.mark (c i))

/-- Records consumed by the rounded complex multiplication command. -/
def cells (i : I) : List (Dusk.Pair × Grid.Orb) :=
  ((branches k rows i).map Dusk.mark).map fun a => (a, header k c i)

theorem branches_length (i : I) : (branches k rows i).length = 2 * (rows i).length := by
  unfold branches
  induction rows i with
  | nil => simp
  | cons p l ih => simp [ih, Nat.mul_add]

theorem cells_length (i : I) : (cells k rows c i).length = 2 * (rows i).length := by
  simp [cells, branches_length]

private theorem header_size (i : I) : size (header k c i) = 524 * k i + 27 := by
  rw [header, size_prod, record_size, size_tally, tally_length, fractionBits]
  omega

/-- All multiplication cells, including the ruler and the scale, have linear
width in the address parameter. -/
theorem cells_width (i : I) (z : Dusk.Pair × Grid.Orb) (hz : z ∈ cells k rows c i) :
    size z ≤ 1200 * (k i + 1) := by
  rcases List.mem_map.mp hz with ⟨a, ha, rfl⟩
  rcases List.mem_map.mp ha with ⟨b, _, rfl⟩
  rw [size_prod, record_size, header_size]
  omega

private def expand (p : Dusk.Pair × Dusk.Pair) : Dusk.Pair × Dusk.Pair :=
  (Dusk.gather p, Dusk.gather (p.1, Dusk.lower p.2))

private theorem expandStream : Easy (fun xs : List (Dusk.Pair × Dusk.Pair) =>
    PairRows.consecutive (xs.map expand)) := by
  have h : Easy expand := by
    unfold expand
    exact Dusk.gather_easy.pair
      ((Easy.fst.pair (Easy.snd.compose Dusk.lower_easy)).compose Dusk.gather_easy)
  exact h.mapping.compose PairRows.unpackPairs

private theorem expand_eq (i : I) :
    PairRows.consecutive ((paired k rows i).map expand) = (branches k rows i).map Dusk.mark := by
  unfold paired branches
  induction rows i with
  | nil => rfl
  | cons p l ih =>
    simpa [expand, butterflySum, sub_eq_add_neg] using ih

private theorem size_map {A B : Type*} [Codec B] (f : A → B) (w : ℕ)
    (hw : ∀ a, size (f a) = w) (l : List A) : size (l.map f) = l.length * (w + 1) + 1 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, hw, Nat.add_mul]; omega

/-- Prepare all the branch-and-scale multiplication records in charged tape
steps, including reading the adjacent operands and replicating the scale. -/
theorem prepare : Task (fun i => ((rows i).length + 1) * (k i + 1))
    (fun i => send (PairRows.consecutive (paired k rows i), header k c i))
    (fun i => send (cells k rows c i)) := by
  have scan := (PairRows.packPairs.on (paired k rows)).compose (expandStream.on (paired k rows))
  simp_rw [expand_eq] at scan
  have stream := scan.left (fun i => send (header k c i))
  have distribute := Cartesian.broadcastRight.on
    (fun i => ((branches k rows i).map Dusk.mark, header k c i))
  apply (stream.compose distribute).bound 5000
  intro i
  have packed : size (paired k rows i) =
      (rows i).length * ((384 * k i + 23) * 2 + 2) + 1 := by
    rw [paired, size_map _ ((384 * k i + 23) * 2 + 1)]
    intro a
    rw [size_prod, record_size, record_size]
    omega
  change size (paired k rows i) + size (paired k rows i) +
    (size ((branches k rows i).map Dusk.mark) +
      (((branches k rows i).map Dusk.mark).length + 1) * size (header k c i)) + 1 ≤ _
  rw [packed, size_map _ _ (record_size (k i)), List.length_map,
    branches_length, header_size]
  nlinarith

end ButterflyTask

end NearSquareRoot
end Computability
end OAI
