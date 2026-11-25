import OAI.Computability.NearSquareRoot.PrecisionProductHeader
import OAI.Computability.NearSquareRoot.PrecisionGridTask
import OAI.Computability.NearSquareRoot.PrecisionGrid
import OAI.Computability.NearSquareRoot.PrecisionBoundedMap
import OAI.Computability.NearSquareRoot.PrecisionProductRelease
import OAI.Computability.NearSquareRoot.PhysicalWalshRelease

/-! # Physical pointwise multiplication of two encoded complex arrays

The inputs have separate address-ordered operand lists and one precision
ruler. Pairing, ruler replication, all signed arithmetic, both fractional
shifts, and the final output copy are charged. The bounded-space execution
reuses the work tapes for every record at a single dispatcher.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ProductPass

open IntegerMultiplication Code FixedPoint

section Adjustment
variable {I : Type} (N k : I → ℕ) (r : I → Tally) (a b : (i : I) → Fin (N i) → Dusk.Pair)

private def tuples (i : I) := List.ofFn fun j => (a i j, r i, b i j)

private def volume (C N k : ℕ) := (4*C+6)*((N+1)*(k+1))

private theorem tupleCap (C : ℕ) (i : I) (j : Fin (N i))
    (ha : size (a i j) ≤ C*(k i+1)) (hb : size (b i j) ≤ C*(k i+1))
    (hr : size (r i) ≤ C*(k i+1)) :
    size (a i j, r i, b i j) ≤ (3*C+2)*(k i+1) := by
  change size (a i j) + (size (r i) + size (b i j) + 1) + 1 ≤ _
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

private theorem prepared (C : ℕ) (ha : ∀ i j, size (a i j) ≤ C*(k i+1))
    (hb : ∀ i j, size (b i j) ≤ C*(k i+1)) (hr : ∀ i, size (r i) ≤ C*(k i+1)) :
    Task (fun i => volume C (N i) (k i)) (fun i => send (List.ofFn (a i), r i, List.ofFn (b i)))
      (fun i => send (tuples N r a b i)) := by
  apply (prepare N (fun i => C*(k i+1)) r a b ha hb hr).mono
  intro i
  unfold volume
  ring_nf
  omega

private theorem queryCap (C : ℕ) (ha : ∀ i j, size (a i j) ≤ C*(k i+1))
    (hb : ∀ i j, size (b i j) ≤ C*(k i+1)) (hr : ∀ i, size (r i) ≤ C*(k i+1)) (i : I) :
    (send (List.ofFn (a i), r i, List.ofFn (b i))).count ≤ volume C (N i) (k i) := by
  change size (_, _, _) ≤ _
  simp only [size_prod, volume]
  have h := hr i
  have hl := streamSize (a i) (ha i)
  have hr := streamSize (b i) (hb i)
  ring_nf at h hl hr ⊢
  omega

private theorem listCap (C : ℕ) (ha : ∀ i j, size (a i j) ≤ C*(k i+1))
    (hb : ∀ i j, size (b i j) ≤ C*(k i+1)) (hr : ∀ i, size (r i) ≤ C*(k i+1)) (i : I) :
    size (tuples N r a b i) ≤ volume C (N i) (k i) := by
  apply (streamSize _ (fun j => tupleCap N k r a b C i j (ha i j) (hb i j) (hr i))).trans
  unfold volume
  ring_nf
  omega

/-- Separate input arrays, a single unary fractional ruler, and one fixed
command, even when the two operands have different component widths. -/
theorem adjustTask (C : ℕ) (ha : ∀ i j, size (a i j) ≤ C*(k i+1))
    (hb : ∀ i j, size (b i j) ≤ C*(k i+1)) (hr : ∀ i, size (r i) ≤ C*(k i+1)) :
    Task (fun i => (N i+1)*GridTask.recordCost (k i))
      (fun i => send (List.ofFn (a i), r i, List.ofFn (b i)))
      (fun i => send (List.ofFn fun j => Grid.adjust (a i j, r i, b i j))) := by
  have h := GridTask.adjustStreamBounded N k (tuples N r a b) (3*C+2)
    (fun i => by simp [tuples]) (by
      intro i z hz
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hz
      exact tupleCap N k r a b C _ _ (ha _ _) (hb _ _) (hr _))
  simp only [tuples, List.map_ofFn, Function.comp_def] at h
  apply ((prepared N k r a b C ha hb hr).compose h).bound (4*C+8)
  intro i
  let T := (N i+1)*GridTask.recordCost (k i)
  have hc : (N i+1)*(k i+1) ≤ T := Nat.mul_le_mul_left _ (GridTask.width_le_recordCost _)
  have hp := Nat.mul_le_mul_left (4*C+6) hc
  have hn : N i * GridTask.recordCost (k i) ≤ T := Nat.mul_le_mul_right _ (by omega)
  change (4*C+6)*_ + _ + 1 ≤ (4*C+8)*(T+1)
  calc
    _ ≤ (4*C+6)*T + T + 1 := by omega
    _ ≤ (4*C+8)*(T+1) := by ring_nf; omega

private theorem outputCap (C : ℕ)
    (hout : ∀ i j, size (Grid.adjust (a i j, r i, b i j)) ≤ C*(k i+1)) (i : I) :
    size ((tuples N r a b i).map Grid.adjust) ≤ volume C (N i) (k i) := by
  simp only [tuples, List.map_ofFn, Function.comp_def]
  apply (streamSize _ (hout i)).trans
  unfold volume
  ring_nf
  omega

private theorem adjustmentBudget (C : ℕ) (ha : ∀ i j, size (a i j) ≤ C*(k i+1))
    (hb : ∀ i j, size (b i j) ≤ C*(k i+1)) (hr : ∀ i, size (r i) ≤ C*(k i+1))
    (hout : ∀ i j, size (Grid.adjust (a i j, r i, b i j)) ≤ C*(k i+1))
    (hN : ∀ i, N i = 2^(k i)) :
    ∃ (W : I → ℕ) (D : ℕ),
      (∀ i z, z ∈ tuples N r a b i →
        GridTask.recordCost (size z) + size (Grid.adjust z) + 1 ≤ W i) ∧
      (∀ i, volume C (N i) (k i) + N i * W i + 1 ≤ D*((N i+1)*GridTask.recordCost (k i))) ∧
      (∀ i, volume C (N i) (k i) + W i + 1 ≤ D*((N i+1)*(k i+1))) := by
  obtain ⟨d, hd⟩ := GridTask.recordCost_scale (3*C+2)
  let W i := (d+C+1)*GridTask.recordCost (k i)
  have hlocal i (z) (hz : z ∈ tuples N r a b i) :
      GridTask.recordCost (size z) + size (Grid.adjust z) + 1 ≤ W i := by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hz
    have hc := GridTask.width_le_recordCost (k i)
    have ht := hd (k i) _ (tupleCap N k r a b C i j (ha i j) (hb i j) (hr i))
    have h := (hout i j).trans (Nat.mul_le_mul_left C hc)
    unfold W
    simp only [Nat.add_mul, one_mul]
    omega
  refine ⟨W, (4*C+6)+(d+C+1)+1, hlocal, ?_, ?_⟩
  · intro i
    let t := (N i+1)*GridTask.recordCost (k i)
    have ht : 1 ≤ t := by change 0 < (N i+1)*GridTask.recordCost (k i); unfold GridTask.recordCost; positivity
    have hV : volume C (N i) (k i) ≤ (4*C+6)*t :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (GridTask.width_le_recordCost _))
    have hW : N i * W i ≤ (d+C+1)*t := by
      change N i * ((d+C+1)*_) ≤ (d+C+1)*((N i+1)*_)
      rw [Nat.mul_left_comm]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
    change _ ≤ ((4*C+6)+(d+C+1)+1)*t
    rw [show ((4*C+6)+(d+C+1)+1)*t = (4*C+6)*t + (d+C+1)*t + t by ring]
    omega
  · intro i
    let v := (N i+1)*(k i+1)
    have hv : 1 ≤ v := by change 0 < (N i+1)*(k i+1); positivity
    have hk : k i + 1 ≤ 2^(k i) := Nat.lt_two_pow_self
    have hlog : Nat.clog 2 (k i+1) ≤ k i := Nat.clog_le_of_le_pow hk
    have hc : GridTask.recordCost (k i) ≤ v := by
      unfold GridTask.recordCost v
      rw [Nat.mul_comm, hN]
      exact Nat.mul_le_mul_right _ (by omega)
    have hw : W i ≤ (d+C+1)*v := Nat.mul_le_mul_left _ hc
    change (4*C+6)*v + W i + 1 ≤ ((4*C+6)+(d+C+1)+1)*v
    rw [show ((4*C+6)+(d+C+1)+1)*v = (4*C+6)*v + (d+C+1)*v + v by ring]
    omega

/-- Time and distinct visited cells of the complete array pass, from loaded
input to the output on a separate physical tape. The clock `k` is the address
width. All three width bounds and the output width are in units of `k+1`. -/
theorem adjustTapePass (C : ℕ) (ha : ∀ i j, size (a i j) ≤ C*(k i+1))
    (hb : ∀ i j, size (b i j) ≤ C*(k i+1)) (hr : ∀ i, size (r i) ≤ C*(k i+1))
    (hout : ∀ i j, size (Grid.adjust (a i j, r i, b i j)) ≤ C*(k i+1))
    (hN : ∀ i, N i = 2^(k i)) :
    ProductDriver.TapePass (fun i => (N i+1)*GridTask.recordCost (k i))
      (fun i => (N i+1)*(k i+1)) (fun i => send (List.ofFn (a i), r i, List.ofFn (b i)))
      (fun i => send (List.ofFn fun j => Grid.adjust (a i j, r i, b i j))) := by
  obtain ⟨W,D,hlocal,ht,hs⟩ := adjustmentBudget N k r a b C ha hb hr hout hN
  have res := ProductDriver.mapOnTapes GridTask.adjustTask (prepared N k r a b C ha hb hr)
    (queryCap N k r a b C ha hb hr) (listCap N k r a b C ha hb hr) (outputCap N k r a b C hout) hlocal
  simp only [tuples, List.length_ofFn, List.map_ofFn, Function.comp_def] at res
  exact res.scale D D ht hs

/-- A single framed command for use inside longer transform executions. -/
theorem adjustBoundedTask (C : ℕ) (ha : ∀ i j, size (a i j) ≤ C*(k i+1))
    (hb : ∀ i j, size (b i j) ≤ C*(k i+1)) (hr : ∀ i, size (r i) ≤ C*(k i+1))
    (hout : ∀ i j, size (Grid.adjust (a i j, r i, b i j)) ≤ C*(k i+1))
    (hN : ∀ i, N i = 2^(k i)) :
    Space.BoundedTask (fun i => (N i+1)*GridTask.recordCost (k i))
      (fun i => (N i+1)*(k i+1)) (fun i => send (List.ofFn (a i), r i, List.ofFn (b i)))
      (fun i => send (List.ofFn fun j => Grid.adjust (a i j, r i, b i j))) := by
  obtain ⟨W,D,hlocal,ht,hs⟩ := adjustmentBudget N k r a b C ha hb hr hout hN
  let xs := tuples N r a b
  let V i := volume C (N i) (k i)
  let Z := (i : I) × Fin (xs i).length
  let arg (v : Z) := (xs v.1)[v.2.val]
  have hw i z (hz : z ∈ xs i) : GridTask.recordCost (size z) ≤ W i := by
    have := hlocal i z hz
    omega
  have call := (GridTask.adjustTask.on arg).mono (fun v => hw v.1 _ (List.getElem_mem _))
  have run := Space.BoundedTask.mapping xs Grid.adjust V W call (listCap N k r a b C ha hb hr)
    (outputCap N k r a b C hout) (fun i z hz => by
      have := GridTask.width_le_recordCost (size z)
      have := hw i z hz
      omega)
  have full := (Space.BoundedTask.of_time (prepared N k r a b C ha hb hr)).compose run
  simp only [xs, tuples, List.length_ofFn, List.map_ofFn, Function.comp_def] at full
  apply full.bound (3*D+2) (2*D+2)
  · intro i
    have h := ht i
    have hn : N i ≤ V i := by unfold V volume; ring_nf; omega
    change V i + N i*W i + 1 ≤ _ at h
    change V i + (V i + N i*(W i+1)) + 1 ≤ _
    rw [Nat.mul_add, Nat.mul_one]
    generalize (N i+1)*GridTask.recordCost (k i) = T at *
    ring_nf at h ⊢
    omega
  · intro i
    have h := hs i
    change V i + W i + 1 ≤ _ at h
    have hq := queryCap N k r a b C ha hb hr i
    change _ ≤ V i at hq
    change max (_ + V i) (V i + W i) + 1 ≤ _
    generalize (N i+1)*(k i+1) = S at h ⊢
    ring_nf at h ⊢
    omega
end Adjustment

variable {I : Type} (N k : I → ℕ) (x y : (i : I) → Fin (N i) → Record (k i))

/-- Framed multiplication from the two operand streams alone. The machine
derives its fractional header from the right operand, whose record width
can differ from that of the left data records. -/
theorem adjustSeparate (q : I → ℕ) (a : (i : I) → Fin (N i) → Dusk.Pair)
    (b : (i : I) → Fin (N i) → Record (q i)) (C : ℕ)
    (ha : ∀ i j, size (a i j) ≤ C*(k i+1))
    (hb : ∀ i j, size (Dusk.mark (b i j)) ≤ C*(k i+1))
    (hr : ∀ i, size (tally (fractionBits (q i))) ≤ C*(k i+1))
    (hout : ∀ i j, size (Grid.adjust (a i j, tally (fractionBits (q i)), Dusk.mark (b i j)))
      ≤ C*(k i+1)) (hN : ∀ i, N i = 2^(k i)) :
    Space.BoundedTask (fun i => (N i+1)*GridTask.recordCost (k i)) (fun i => (N i+1)*(k i+1))
      (fun i => send (List.ofFn (a i), List.ofFn fun j => Dusk.mark (b i j)))
      (fun i => send (List.ofFn fun j => Grid.adjust (a i j, tally (fractionBits (q i)), Dusk.mark (b i j)))) := by
  have head := headerFromArrays N k q a b C ha hb (fun i => hN i ▸ Nat.two_pow_pos _)
  have run := adjustBoundedTask N k (fun i => tally (fractionBits (q i))) a
    (fun i j => Dusk.mark (b i j)) C ha hb hr hout hN
  apply (head.compose run).bound 2 1
  · intro i
    have := Nat.mul_le_mul_left (N i+1) (GridTask.width_le_recordCost (k i))
    omega
  · simp

private theorem storedSize {k : ℕ} (x : Record k) : size (Dusk.mark x) ≤ 384*(k+1) := by
  rw [record_size]
  omega

private theorem fractionSize (k : ℕ) : size (tally (fractionBits k)) ≤ 384*(k+1) := by
  simp only [size_tally, tally_length, fractionBits]
  omega

/-- The inputs, precision header, rounded arithmetic and result order of a
pointwise product in the transform record format. -/
theorem pointwiseTapePass (hN : ∀ i, N i = 2^(k i)) :
    ProductDriver.TapePass (fun i => (N i+1)*GridTask.recordCost (k i))
      (fun i => (N i+1)*(k i+1))
      (fun i => send (List.ofFn (fun j => Dusk.mark (x i j)), tally (fractionBits (k i)),
        List.ofFn (fun j => Dusk.mark (y i j))))
      (fun i => send (List.ofFn fun j => Dusk.mark (multiply (k i) (x i j) (y i j)))) := by
  have r := adjustTapePass N k (fun i => tally (fractionBits (k i)))
    (fun i j => Dusk.mark (x i j)) (fun i j => Dusk.mark (y i j)) 384
    (fun i j => storedSize (x i j)) (fun i j => storedSize (y i j))
    (fun i => fractionSize (k i)) (fun i j => by rw [multiply_encoding]; exact storedSize _) hN
  simpa only [multiply_encoding] using r

/-- Framed form of the transform-record pointwise product. -/
theorem pointwiseBoundedTask (hN : ∀ i, N i = 2^(k i)) :
    Space.BoundedTask (fun i => (N i+1)*GridTask.recordCost (k i))
      (fun i => (N i+1)*(k i+1))
      (fun i => send (List.ofFn (fun j => Dusk.mark (x i j)), tally (fractionBits (k i)),
        List.ofFn (fun j => Dusk.mark (y i j))))
      (fun i => send (List.ofFn fun j => Dusk.mark (multiply (k i) (x i j) (y i j)))) := by
  have r := adjustBoundedTask N k (fun i => tally (fractionBits (k i)))
    (fun i j => Dusk.mark (x i j)) (fun i j => Dusk.mark (y i j)) 384
    (fun i j => storedSize (x i j)) (fun i j => storedSize (y i j))
    (fun i => fractionSize (k i)) (fun i j => by rw [multiply_encoding]; exact storedSize _) hN
  simpa only [multiply_encoding] using r

/-- Full pointwise product command requiring only the two serialized arrays. -/
theorem pointwiseSeparate (hN : ∀ i, N i = 2^(k i)) :
    Space.BoundedTask (fun i => (N i+1)*GridTask.recordCost (k i)) (fun i => (N i+1)*(k i+1))
      (fun i => send (List.ofFn (fun j => Dusk.mark (x i j)), List.ofFn (fun j => Dusk.mark (y i j))))
      (fun i => send (List.ofFn fun j => Dusk.mark (multiply (k i) (x i j) (y i j)))) := by
  have run := adjustSeparate N k k (fun i j => Dusk.mark (x i j)) y 384
    (fun i j => storedSize (x i j)) (fun i j => storedSize (y i j)) (fun i => fractionSize _)
    (fun i j => by rw [multiply_encoding]; exact storedSize _) hN
  simpa only [multiply_encoding] using run

/-- Physical run with only the two operands loaded. The clock includes
header generation, arithmetic, and writing the entire pointwise product
onto a separate output tape. -/
theorem pointwiseSeparateTapes (hN : ∀ i, N i = 2^(k i)) :
    ∃ C : ℕ, PhysicalWalsh.TapeRun (fun i => C*((N i+1)*GridTask.recordCost (k i)+1))
      (fun i => C*((N i+1)*(k i+1)+1))
      (fun i => send (List.ofFn (fun j => Dusk.mark (x i j)), List.ofFn (fun j => Dusk.mark (y i j))))
      (fun i => send (List.ofFn fun j => Dusk.mark (multiply (k i) (x i j) (y i j)))) :=
  (pointwiseSeparate N k x y hN).releaseOfSpaceLeTime (fun i =>
    Nat.mul_le_mul_left _ (GridTask.width_le_recordCost (k i)))

end ProductPass

end NearSquareRoot
end Computability
end OAI
