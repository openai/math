import OAI.Computability.IntegerMultiplication.Code.Dup
import OAI.Computability.NearSquareRoot.CartesianSize
import Mathlib.Tactic

/-! # Cartesian products of encoded streams

To build a row, replicate the prefix record using a unary ruler read from the
local table, then zip it with the table. To build the entire stream, use the
same procedure to attach a private copy of the table to every prefix. All
replications, zips and list traversals use the P192 stack commands.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Cartesian

open IntegerMultiplication.Code

variable {X Y : Type*} [Codec X] [Codec Y]

private theorem sizeReplicate (n : ℕ) (x : X) :
    size (List.replicate n x) = n * (size x + 1) + 1 := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, Nat.succ_mul]; omega

omit [Codec X] [Codec Y] in
private theorem zipConstantRight (l : List X) (y : Y) :
    l.zip (List.replicate l.length y) = l.map fun x => (x,y) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.replicate_succ, ih]

omit [Codec X] [Codec Y] in
private theorem zipConstantLeft (x : X) (l : List Y) :
    (List.replicate l.length x).zip l = l.map fun y => (x,y) := by
  induction l with
  | nil => rfl
  | cons y l ih => simp [List.replicate_succ, ih]

/-- Copy one right-hand value into every record of a stream, preserving order. -/
theorem broadcastRight :
    Computes (fun s : List X × Y => size s.1 + (s.1.length + 1) * size s.2)
      (fun s => s.1.map fun x => (x, s.2)) := by
  let copies (s : List X × Y) := List.replicate s.1.length s.2
  have prep : Easy (fun s : List X × Y => (s.1, ruler s.1, s.2)) := by fun_prop
  have dup := (generate.on (fun s : List X × Y => (ruler s.1,s.2))).right
    (fun s => send s.1)
  simp only [ruler_length] at dup
  have alg := (Task.compose prep dup).compose <| zip_spec.on
    (fun s : List X × Y => ⟨(s.1, copies s), by simp [copies]⟩)
  simpa only [copies, zipConstantRight] using (alg.bound 6 (b' := fun s =>
    size s.1 + (s.1.length + 1) * size s.2) (fun s => by
      change size s + (size s.1 + (s.1.length+1)*size s.2) +
          size (s.1,copies s) + 1 ≤ _
      simp only [copies, size_prod, sizeReplicate, Nat.add_mul, Nat.mul_add,
        Nat.mul_one, Nat.one_mul]
      have hlen := Nat.le_mul_of_pos_right s.1.length (size_pos s.2)
      omega))

/-- Form one row of pairs with a common left-hand record. -/
theorem broadcastLeft :
    Computes (fun s : X × List Y => (s.2.length + 1) * size s.1 + size s.2)
      (fun s => s.2.map fun y => (s.1,y)) := by
  let copies (s : X × List Y) := List.replicate s.2.length s.1
  have prep : Easy (fun s : X × List Y => ((ruler s.2,s.1),s.2)) := by fun_prop
  have dup := (generate.on (fun s : X × List Y => (ruler s.2,s.1))).left
    (fun s => send s.2)
  simp only [ruler_length] at dup
  have alg := (Task.compose prep dup).compose <| zip_spec.on
    (fun s : X × List Y => ⟨(copies s,s.2), by simp [copies]⟩)
  simpa only [copies, zipConstantLeft] using (alg.bound 6 (b' := fun s =>
    (s.2.length + 1) * size s.1 + size s.2) (fun s => by
      change size s + (s.2.length+1)*size s.1 + size (copies s,s.2) + 1 ≤ _
      simp only [copies, size_prod, sizeReplicate, Nat.add_mul, Nat.mul_add,
        Nat.mul_one, Nat.one_mul]
      have hlen := Nat.le_mul_of_pos_right s.2.length (size_pos s.1)
      omega))

/-- The command also accepts empty streams and charges their initial scan. -/
theorem cartesianAll :
    Computes (fun s : List X × List Y =>
      size s.1 * (s.2.length+1) + size s.2 * (s.1.length+1))
      (fun s => s.1.flatMap fun x => s.2.map fun y => (x,y)) := by
  let rows (s : List X × List Y) := s.1.map fun x => (x,s.2)
  let outputs (s : List X × List Y) := s.1.map fun x => s.2.map fun y => (x,y)
  have run := broadcastRight.compose ((broadcastLeft (X := X) (Y := Y)).mapping.on rows)
  have flat := (Easy.flatten (X := X × Y)).on outputs
  simp only [rows, List.map_map, Function.comp_def] at run
  apply (run.compose flat).bound 5
  intro s
  have h := cartesian_row_budget s.1 s.2
  change size s.1 + (s.1.length + 1) * size s.2 +
    (size (rows s) + costSum _ (rows s)) + size (outputs s) + 1 ≤ _
  have hinput : size s.1 ≤ size s.1 * (s.2.length+1) := Nat.le_mul_of_pos_right _ (by omega)
  change size (rows s) + costSum _ (rows s) + size (outputs s) ≤ _ at h
  rw [Nat.mul_comm (s.1.length+1) (size s.2)]
  omega

/-- Lexicographic Cartesian product, charging each input symbol once per
record on the opposite side. -/
theorem cartesian {I : Type*} (l : I → List X) (r : I → List Y)
    (hl : ∀ i, l i ≠ []) (hr : ∀ i, r i ≠ []) :
    Task (fun i => size (l i) * (r i).length + size (r i) * (l i).length)
      (fun i => send (l i,r i))
      (fun i => send ((l i).flatMap fun x => (r i).map fun y => (x,y))) := by
  apply (cartesianAll.on (fun i => (l i,r i))).bound 2
  intro i
  have hl' := List.length_pos_iff.mpr (hl i)
  have hr' := List.length_pos_iff.mpr (hr i)
  have := Nat.le_mul_of_pos_right (size (l i)) hr'
  have := Nat.le_mul_of_pos_right (size (r i)) hl'
  simp only [Nat.mul_add, Nat.mul_one]
  omega

end Cartesian

end NearSquareRoot
end Computability
end OAI
