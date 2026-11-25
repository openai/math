import OAI.Computability.NearSquareRoot.PrecisionFlatWalshBits
import OAI.Computability.IntegerMultiplication.Grid.Value
import Mathlib.Data.Finset.Sort

/-! # Exact integer butterflies on selected packed address bits

Each selected bit contributes one round of signed integer additions. The
other address bits retain their original fiber and the common normalization
is deferred until all rounds finish.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatWalshInteger

open IntegerMultiplication Finset Matrix

variable {k : ℕ}

/-- Add or subtract the two integer records at a selected bit. -/
def butterfly (p : Fin k) (x : Fin (2^k) → Grid.Cell) (a : Fin (2^k)) : Grid.Cell :=
  x (flip p a) + if a.val.testBit p.val then -x a else x a

/-- Materialize each complete round so both outputs of every butterfly
read from the same stored input vector. -/
def passes : List (Fin k) → (Fin (2^k) → Grid.Cell) → Vector Grid.Cell (2^k)
  | [], x => Vector.ofFn x
  | p :: ps, x =>
    let previous := passes ps x
    Vector.ofFn (butterfly p (fun j => previous[j.val]))

/-- The integer Walsh numerator, by one butterfly round per selected bit. -/
def transform (bits : Finset (Fin k)) (x : Fin (2^k) → Grid.Cell) : Fin (2^k) → Grid.Cell :=
  fun a => (passes bits.sort x)[a.val]

private noncomputable def weight (s : Finset (Fin k)) (a b : Fin (2^k)) : ℂ := by
  classical
  exact if BoxFin.offBits s a b then (-1)^BoxFin.physicalOverlap s a b else 0

private theorem offBits_insert (s : Finset (Fin k)) {p : Fin k} (hp : p ∉ s) (a b : Fin (2^k)) :
    BoxFin.offBits s a b ↔ BoxFin.offBits (insert p s) a b ∧
      a.val.testBit p.val = b.val.testBit p.val := by
  constructor
  · intro h
    exact ⟨fun q hq => h q (fun hqs => hq (mem_insert_of_mem hqs)), h p hp⟩
  · rintro ⟨h,hp'⟩ q hq
    by_cases eq : q = p
    · simpa only [eq] using hp'
    · exact h q (by simp [eq,hq])

private theorem offBits_flip (s : Finset (Fin k)) {p : Fin k} (hp : p ∉ s) (a b : Fin (2^k)) :
    BoxFin.offBits s (flip p a) b ↔ BoxFin.offBits (insert p s) a b ∧
      (!(a.val.testBit p.val)) = b.val.testBit p.val := by
  rw [offBits_insert s hp, testBit_flip]
  simp only [ite_true]
  suffices BoxFin.offBits (insert p s) (flip p a) b ↔ BoxFin.offBits (insert p s) a b by
    rw [this]
  constructor <;> intro h q hq <;>
    have hn : q ≠ p := fun he => hq (he ▸ mem_insert_self ..)
  · simpa only [testBit_flip, ite_eq_right hn] using h q hq
  · simpa only [testBit_flip, ite_eq_right hn] using h q hq

private theorem overlap_flip (s : Finset (Fin k)) {p : Fin k} (hp : p ∉ s) (a b : Fin (2^k)) :
    BoxFin.physicalOverlap s (flip p a) b = BoxFin.physicalOverlap s a b := by
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro q hq
  have hn : q ≠ p := fun he => hp (he ▸ hq)
  simp only [testBit_flip, ite_eq_right hn]

private theorem overlap_insert (s : Finset (Fin k)) {p : Fin k} (hp : p ∉ s) (a b : Fin (2^k)) :
    BoxFin.physicalOverlap (insert p s) a b = BoxFin.physicalOverlap s a b +
      (if a.val.testBit p.val ∧ b.val.testBit p.val then 1 else 0) := by
  simp only [BoxFin.physicalOverlap, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun hm => hp (Finset.mem_filter.mp hm).1)]
  · simp

private theorem weight_insert (s : Finset (Fin k)) {p : Fin k} (hp : p ∉ s) (a b : Fin (2^k)) :
    weight (insert p s) a b =
      weight s (flip p a) b + (if a.val.testBit p.val then -weight s a b else weight s a b) := by
  classical
  simp only [weight, offBits_flip s hp, offBits_insert s hp, overlap_insert s hp, overlap_flip s hp]
  by_cases h : BoxFin.offBits (insert p s) a b <;>
    cases ha : a.val.testBit p.val <;> cases hb : b.val.testBit p.val <;>
      simp [h, pow_succ]

private theorem passes_eq (ps : List (Fin k)) (hn : ps.Nodup) (x : Fin (2^k) → Grid.Cell)
    (a : Fin (2^k)) :
    Grid.toC ((passes ps x)[a.val]) = ∑ b, weight ps.toFinset a b * Grid.toC (x b) := by
  classical
  induction ps generalizing a with
  | nil =>
    simp [passes, weight, offBits_empty_iff, BoxFin.physicalOverlap]
  | cons p ps ih =>
    have hp : p ∉ ps.toFinset := by simpa only [List.mem_toFinset] using hn.notMem
    simp only [passes, Vector.getElem_ofFn, butterfly, map_add, List.toFinset_cons, weight_insert _ hp]
    by_cases ha : a.val.testBit p.val <;>
      simp [ha, ih hn.tail, Finset.sum_add_distrib, add_mul]

/-- Normalizing the exact integer evaluator recovers the full selected-bit
matrix on the packed array, including its spectator coordinates. -/
theorem normalized_transform (bits : Finset (Fin k)) (x : Fin (2^k) → Grid.Cell) (a : Fin (2^k)) :
    (SynchronizedPair.w : ℂ)^bits.card * Grid.toC (transform bits x a) =
      (BoxFin.flatWalsh bits *ᵥ (fun j => Grid.toC (x j))) a := by
  classical
  rw [transform, passes_eq _ (Finset.sort_nodup ..), Finset.sort_toFinset, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : BoxFin.offBits bits a b <;> simp [weight, BoxFin.flatWalsh, h, mul_assoc]

end FlatWalshInteger

end NearSquareRoot
end Computability
end OAI
