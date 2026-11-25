import OAI.Computability.NearSquareRoot.PrecisionGridStreamTask

/-! # From raw local coefficient tables to the phase-extension input

The packet contains two unary rulers followed by the ordered list of raw
coefficient tables. The program copies the fractional ruler into each local
coefficient and constructs the one-element prefix containing the fixed-point
encoding of one.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication Code

/-- The preparation protocol reads both rulers once from its packet. -/
abbrev RawPhasePacket := (Tally × Tally) × List (List Dusk.Pair)

def rawPhasePacket {w : ℕ} (f : ℕ) (rows : List (List (Dusk.Grain w))) : RawPhasePacket :=
  ((tally f, tally (w + 1)), rows.map (List.map Dusk.mark))

private def seededPacket (p : RawPhasePacket) :=
  ((p.1.1, p.2), [encodeDigit ([true], p.1)])

private theorem seededPacket_easy : Easy seededPacket := by
  unfold seededPacket
  fun_prop

/-- Amount of work for two broadcasts, first across rows and then within each row. -/
private def headerCost (p : Tally × List (List Dusk.Pair)) : ℕ :=
  (p.2.length + 1) * size p.1 + size p.2 +
    (size (p.2.map fun r => (p.1, r)) + costSum
      (fun x : Tally × List Dusk.Pair => (x.2.length + 1) * size x.1 + size x.2)
      (p.2.map fun r => (p.1, r)))

private theorem attachHeaders :
    Computes headerCost (fun p : Tally × List (List Dusk.Pair) =>
      p.2.map fun r => r.map fun x => (p.1, x)) := by
  have rows := Cartesian.broadcastLeft (X := Tally) (Y := List Dusk.Pair)
  have words := (Cartesian.broadcastLeft (X := Tally) (Y := Dusk.Pair)).mapping
  have run := rows.compose (words.on (fun p : Tally × List (List Dusk.Pair) =>
    p.2.map fun r => (p.1, r)))
  apply run.conform (fun _ => rfl) (fun _ => rfl)
  intro p
  simp only [List.map_map, Function.comp_def]

private theorem seedMark (k : ℕ) :
    encodeDigit ([true], tally (fractionBits k), tally (componentBits k + 1)) =
      Dusk.mark (digitRecord k 1) := by
  exact encodeDigit_eq (k := k) [true]
    (show 1 ≤ 2 ^ (13*k) from Nat.one_le_pow _ _ (by decide))

/-- A single traversal of the supplied packet followed by the two ruler broadcasts. -/
private theorem rawPacketRun {I : Type*} (k : I → ℕ)
    (rows : (i : I) → List (List (Record (k i)))) :
    let p i := rawPhasePacket (fractionBits (k i)) (rows i)
    Task (fun i => size (p i) + headerCost ((p i).1.1, (p i).2))
      (fun i => send (p i))
      (fun i => .fork
        (send ((rows i).map fun r => r.map fun x => (tally (fractionBits (k i)), Dusk.mark x)))
        (send [Dusk.mark (digitRecord (k i) 1)])) := by
  dsimp only
  let p i := rawPhasePacket (fractionBits (k i)) (rows i)
  let r i := ((p i).1.1, (p i).2)
  have attach := (attachHeaders.on r).left (fun i => send (seededPacket (p i)).2)
  have run := (seededPacket_easy.on p).compose attach
  refine run.conform (fun _ => rfl) (fun _ => rfl) ?_
  intro i
  simp only [r, p, seededPacket, rawPhasePacket, List.map_map, Function.comp_def, seedMark]

private def rowUnits {α : Type*} (rows : List (List α)) : ℕ :=
  (rows.map (fun r => r.length + 1)).sum + 1

private theorem rawSize {w : ℕ} (r : List (Dusk.Grain w)) :
    size (r.map Dusk.mark) ≤ 10 * (r.length * (w + 1)) + 1 := by
  induction r with
  | nil => simp
  | cons x r ih =>
    simp only [List.map_cons, size_cons, Dusk.volume, List.length_cons, Nat.succ_mul]
    omega

private theorem rawPacketCost {w f : ℕ} (rows : List (List (Dusk.Grain w))) (hf : f ≤ w+1) :
    let p := rawPhasePacket f rows
    2 * size p + headerCost (p.1.1, p.2) + 1 ≤ 100 * (rowUnits rows * (w+1)) := by
  dsimp only
  induction rows with
  | nil =>
    simp only [rawPhasePacket, List.map_nil, size_prod, size_tally, tally_length,
      size_nil, headerCost, List.length_nil, costSum_nil, rowUnits, List.sum_nil,
      Nat.zero_add, Nat.one_mul]
    omega
  | cons x xs ih =>
    simp only [rawPhasePacket, List.map_cons, size_prod, size_tally, tally_length,
      size_cons, headerCost, List.length_cons, List.length_map, costSum_cons, rowUnits,
      List.sum_cons] at ih ⊢
    have hx := rawSize x
    have hh : x.length * (2 * f + 1) ≤ 3 * (x.length * (w + 1)) := by
      have it := Nat.mul_le_mul_left x.length (show 2*f+1 ≤ 3*(w+1) by omega)
      nlinarith only [it]
    simp only [Nat.add_mul, Nat.one_mul] at *
    omega

private theorem rowUnits_le_prod {α : Type*} (rows : List (List α))
    (hrows : ∀ r ∈ rows, 2 ≤ r.length) :
    0 < (rows.map List.length).prod ∧ rowUnits rows ≤ 3 * (rows.map List.length).prod := by
  induction rows with
  | nil => simp [rowUnits]
  | cons r rows ih =>
    obtain ⟨pos, sum⟩ := ih (fun s hs => hrows s (List.mem_cons_of_mem _ hs))
    have h := hrows r List.mem_cons_self
    simp only [List.map_cons, List.prod_cons]
    refine ⟨Nat.mul_pos (by omega) pos, ?_⟩
    have len := Nat.mul_le_mul_left (r.length - 1) pos
    have decomp := Nat.sub_add_cancel (by omega : 1 ≤ r.length)
    have eq := congrArg (· * (rows.map List.length).prod) decomp
    simp only [Nat.add_mul, Nat.one_mul] at eq
    simp only [rowUnits, List.map_cons, List.sum_cons] at sum ⊢
    omega

/-- Both rulers and the raw words are part of the serialized input. -/
def phaseTablePacket (k : ℕ) (rows : List (List (Record k))) : Tree :=
  send (rawPhasePacket (w := componentBits k) (fractionBits k) rows)

/-- The first field is the table forest, the second the seed prefix. -/
def phaseTableSeed (k : ℕ) (rows : List (List (Record k))) : Tree :=
  .fork (send (rows.map fun r => r.map fun x => (tally (fractionBits k), Dusk.mark x)))
    (send [Dusk.mark (digitRecord k 1)])

/-- With at least two entries per supplied table, preparing all table packets
and the unit prefix costs linear time and space in the final number of records
times their precision. The empty list of tables has final record count one. -/
theorem phaseTableInput_bounded {I : Type*} (k : I → ℕ)
    (rows : (i : I) → List (List (Record (guardedK (k i)))))
    (hrows : ∀ i r, r ∈ rows i → 2 ≤ r.length) :
    let V i := ((rows i).map List.length).prod * (k i + 1)
    Space.BoundedTask V V
      (fun i => phaseTablePacket (guardedK (k i)) (rows i))
      (fun i => phaseTableSeed (guardedK (k i)) (rows i)) := by
  have run := Space.BoundedTask.of_time (rawPacketRun (fun i => guardedK (k i)) rows)
  have bound (i : I) := rawPacketCost (w := componentBits (guardedK (k i)))
    (f := fractionBits (guardedK (k i))) (rows i)
    (show fractionBits (guardedK (k i)) ≤ componentBits (guardedK (k i))+1 by
      unfold fractionBits componentBits
      omega)
  have total (i : I) := (rowUnits_le_prod (rows i) (hrows i)).2
  have final (i : I) : 100 * (rowUnits (rows i) * (componentBits (guardedK (k i))+1)) ≤
      90000 * (((rows i).map List.length).prod * (k i + 1)) := by
    have hw : componentBits (guardedK (k i))+1 ≤ 300*(k i+1) := by
      unfold componentBits guardedK
      omega
    have hh := Nat.mul_le_mul (total i) hw
    nlinarith only [hh]
  let packet (i : I) := rawPhasePacket (w := componentBits (guardedK (k i)))
    (fractionBits (guardedK (k i))) (rows i)
  apply run.bound 90000 90000
  · intro i
    have h := (bound i).trans (final i)
    change 2*size (packet i) + headerCost ((packet i).1.1, (packet i).2) + 1 ≤ _ at h
    change size (packet i) + headerCost ((packet i).1.1, (packet i).2) + 1 ≤ _
    omega
  · intro i
    have h := (bound i).trans (final i)
    change 2*size (packet i) + headerCost ((packet i).1.1, (packet i).2) + 1 ≤ _ at h
    change size (packet i) + (size (packet i) + headerCost ((packet i).1.1, (packet i).2)) + 1 ≤ _
    omega

/-- In coordinate order the physical output is exactly the encoded input of
the framed phase-extension passes. -/
theorem phaseTableInput_indexed {I : Type*} (k d : I → ℕ)
    (t : (i : I) → ℕ → List (Record (guardedK (k i))))
    (ht : ∀ i j, j < d i → 2 ≤ (t i j).length) :
    let V i := ((List.range (d i)).map (fun j => (t i j).length)).prod * (k i + 1)
    Space.BoundedTask V V
      (fun i => phaseTablePacket (guardedK (k i)) ((List.range (d i)).map (t i)))
      (fun i => .fork
        (send ((List.range (d i)).map fun j => tableWords (fractionBits (guardedK (k i))) (t i j)))
        (send (prefixWords [digitRecord (guardedK (k i)) 1]))) := by
  have run := phaseTableInput_bounded k (fun i => (List.range (d i)).map (t i))
    (fun i r hr => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      exact ht i j (List.mem_range.mp hj))
  apply run.conform (fun _ => by simp [List.map_map, Function.comp_def])
    (fun _ => by simp [List.map_map, Function.comp_def]) (fun _ => rfl)
  intro i
  simp [phaseTableSeed, prefixWords, tableWords, List.map_map, Function.comp_def]

/-- The full register program from the two rulers and raw local rows to the
numerical phase stream, including the forward error for the words it writes. -/
theorem rawPhaseStream {I α : Type} (k d : I → ℕ) (t : I → ℕ → List α)
    (store : (i : I) → α → Record (guardedK (k i))) (ideal : I → α → ℂ)
    (hd : ∀ i, d i ≤ k i) (ht : ∀ i j, j < d i → 2 ≤ (t i j).length)
    (hunit : ∀ i j, j < d i → ∀ a ∈ t i j, ‖ideal i a‖ = 1)
    (herr : ∀ i j, j < d i → ∀ a ∈ t i j,
      ‖value _ (store i a) - ideal i a‖ ≤ 1 / (2 : ℝ) ^ (70 * guardedK (k i))) :
    let r i := phaseStreamRecords (k i) (t i) (store i) (d i)
    let packet i := phaseTablePacket (guardedK (k i))
      ((List.range (d i)).map (fun j => (t i j).map (store i)))
    Space.BoundedTask (fun i => (r i).length * GridTask.recordCost (k i))
      (fun i => (r i).length * (k i + 1) + GridTask.recordCost (k i)) packet
      (fun i => send (prefixWords (r i))) ∧
    ∀ i, List.Forall₂ (fun v z => ‖value _ v - z‖ ≤ 1 / (2 : ℝ) ^ (70 * k i)) (r i)
      ((PhaseStream.addresses ((List.range (d i)).map (t i))).map (fun xs => (xs.map (ideal i)).prod)) := by
  obtain ⟨⟨passes, _⟩, accuracy⟩ := physicalPhaseStream k d t store ideal hd ht hunit herr
  refine ⟨?_, accuracy⟩
  have prep := phaseTableInput_indexed k d (fun i j => (t i j).map (store i))
    (fun i j hj => by simpa using ht i j hj)
  have chain := prep.compose passes
  apply chain.bound 2 1
  · intro i
    simp only [List.length_map, phaseStreamRecords_count]
    have h := Nat.mul_le_mul_left (((List.range (d i)).map (fun j => (t i j).length)).prod)
      (GridTask.width_le_recordCost (k i))
    omega
  · intro i
    simp only [List.length_map, phaseStreamRecords_count, Nat.one_mul]
    omega

end FixedPoint

end NearSquareRoot
end Computability
end OAI
