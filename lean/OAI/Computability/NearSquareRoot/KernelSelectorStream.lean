import OAI.Computability.IntegerMultiplication.Adic.Grow
import OAI.Computability.NearSquareRoot.KernelSelectorDecode
import OAI.Computability.NearSquareRoot.KernelSelectorTable

/-!
# Streaming a binary kernel's selectors from the address width

The address words are generated on the work tapes, without an explicit input
address per record. The P192 generator writes every word, including leading
zeroes, in lexicographic order. The table lookup parses each complete address
and selects one entry before continuing to the next address.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelSelector

open IntegerMultiplication IntegerMultiplication.Code
open Adic (Raw shoots)
open KernelSelectorAlign

private theorem binary_digit_size (i : Fin 2) : size i + 1 ≤ 4 := by
  change size (tally i.val) + 1 ≤ 4
  rw [size_tally, tally_length]
  omega

private theorem width_of_mem {v : Tally} {w : Raw 2} (hw : w ∈ shoots 2 v) :
    w.length = v.length := by
  obtain ⟨x, rfl⟩ := (Strip.Series.elements ..).mp hw
  exact Adic.length x

/-- A selector with a linear-cost program on each width-k address can be
tabulated in address order in O((k+1)2^k) steps, starting with only k in unary.
The value computation may use a promised shape parameter that is never read
by the machine. -/
theorem generateTable {F Y : Type} [Codec Y] (k : F → ℕ) (value : F → Raw 2 → Y)
    (one : Task (fun u : {s : F × Raw 2 // s.2.length = k s.1} => k u.val.1)
      (fun u => send u.val.2) (fun u => send (value u.val.1 u.val.2))) :
    Task (fun x => (k x + 1)*2^k x) (fun x => send (tally (k x)))
      (fun x => send ((shoots 2 (tally (k x))).map (value x))) := by
  let words (x : F) := shoots 2 (tally (k x))
  let dom (x : F) : {p : F × List (Raw 2) // ∀ w ∈ p.2, w.length = k p.1} :=
    ⟨(x,words x), fun _ hw => (width_of_mem hw).trans (tally_length _)⟩
  have many := (Task.mapTask F (fun _ => send (X := Raw 2))
    (fun x w => send (value x w)) (a := fun x _ => k x)
    (B := fun x w => w.length = k x) one).on dom
  have encoded (x : F) :
      Task.forest (fun w => send (value x w)) (words x) = send ((words x).map (value x)) :=
    (Task.forest_map send (value x) _).symm.trans (Task.forest_send _)
  dsimp only [dom] at many
  simp only [Task.forest_send, encoded] at many
  have gen := (Adic.generate 2 (by decide)).on (fun x : F => tally (k x))
  simp only [tally_length] at gen
  apply (gen.compose many).bound 10
  intro x
  have sz := Adic.tally_bound 2 4 binary_digit_size (tally (k x))
  simp only [tally_length] at sz
  have cc : costSum (fun _ : Raw 2 => k x) (words x) = 2 ^ k x * k x := by
    simp [costSum, words, List.map_const']
  change (k x+1)*2^k x+(costSum (fun _ : Raw 2 => k x) (words x)+size (words x))+1 ≤ _
  rw [cc]
  dsimp only [words]
  nlinarith [Nat.zero_le (2 ^ k x)]

def digitBit (i : Fin 2) := decide (i.val = 1)

/-- All addresses in physical slot order, decoded into rectangular columns. -/
def addressColumns (a f : ℕ) : List (List (Column a)) :=
  (shoots 2 (tally ((a+1)*f))).map fun w => decode a f (w.map digitBit)

/-- Generate any finite table whose slot-major address lookup is physically linear. -/
theorem generateColumnTable {a : ℕ} {Y : Type} [Codec Y] (v : List (Column a) → Y)
    (lookup : Task List.length (fun xs => send (flatBits a xs)) (fun xs => send (v xs))) :
    Task (fun f => ((a+1)*f+1) * 2^((a+1)*f))
      (fun f => send (tally ((a+1)*f))) (fun f => send ((addressColumns a f).map v)) := by
  simp only [addressColumns, List.map_map, Function.comp_def]
  apply generateTable (k := fun f => (a+1)*f)
    (value := fun f w => v (decode a f (w.map digitBit)))
  let U := {s : ℕ × Raw 2 // s.2.length = (a+1)*s.1}
  let columns (u : U) := decode a u.val.1 (u.val.2.map digitBit)
  have good (u : U) : (u.val.2.map digitBit).length = (a+1)*u.val.1 := by
    simpa using u.property
  have flat (u : U) := flatBits_decode a u.val.1 _ (good u)
  have len (u : U) := decode_length a u.val.1 _ (good u)
  have bitMap : Easy (List.map digitBit) := (Easy.finite digitBit).mapping
  have readBits := bitMap.on (fun u : U => u.val.2)
  have look := lookup.on columns
  dsimp only [columns] at look
  simp only [flat, len] at look
  apply (readBits.compose look).bound 6
  intro u
  have sz := Adic.raw_size 2 4 binary_digit_size u.val.2
  rw [u.property] at sz
  have h : u.val.1 ≤ (a+1)*u.val.1 := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- Selected coefficients in the tape order of the full binary addresses. -/
def coefficientStream {a m d : ℕ} {Y : Type} (slot : (Fin (m+1) ⊕ Fin d) × Bool ≃ Fin (a+1))
    (table : (Fin (m+1) → ZMod 2) → Y) (f : ℕ) : List Y :=
  (addressColumns a f).map fun x => table (signature slot x)

/-- The compiled physical program generates the complete stream of selected
coefficients from just the total address width. The running time includes
address generation, slot alignment, spectral signatures, and table lookup. -/
theorem physicalCoefficientStream {a m d : ℕ} {Y : Type} [Codec Y]
    (slot : (Fin (m+1) ⊕ Fin d) × Bool ≃ Fin (a+1))
    (table : (Fin (m+1) → ZMod 2) → Y) :
    ShortWord.PhysicalTask (fun f => ((a+1)*f+1) * 2^((a+1)*f))
      (fun f => send (tally ((a+1)*f))) (fun f => send (coefficientStream slot table f)) :=
  ShortWord.physicalTask (generateColumnTable _ (flatLookup slot table))

end KernelSelector

end NearSquareRoot
end Computability
end OAI
