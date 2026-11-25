import OAI.Computability.BorderVNP.DiagonalTallyScatterLoop
import OAI.Computability.BorderVNP.DiagonalCellLeaves

/-!
# Sparse subtotal records emitted for a private cell

One native record is needed per weighted unary occurrence and per fixed gadget position.
The private cell's own checker accounts for every scalar occurrence, including zero entries,
before reporting the counts of the fixed positions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open Diagonal.CellEntries DiagonalTallyScatter

variable {h u : ℕ}

/-- Emit each unary occurrence's two public words, including a zero increment for
a false use bit. Ordinary tests and private scalar reads emit no unary record. -/
def unaryRecord : Leaf (Fin h) (Fin u) → Option (ℕ × ℕ)
  | .power i j b => some (i.val, if b then 2^j else 0)
  | _ => none

/-- A private cell reports the total number of selections of each fixed gadget entry. -/
def gadgetRecords (h : ℕ) (counts : Fin u → ℕ) : List (ℕ × ℕ) :=
  List.ofFn fun g => (h+g.val, counts g)

/-- Actual sparse stream for a cell with a private assignment and checked counts. -/
noncomputable def cellRecords (ls : List (Leaf (Fin h) (Fin u))) : List (ℕ × ℕ) :=
  ls.filterMap unaryRecord ++ gadgetRecords h (scalarCounts ls)

private theorem increment_append (base a : ℕ) (xs ys : List (ℕ × ℕ)) :
    incrementAt base a (xs++ys) = incrementAt base a xs + incrementAt base a ys := by
  induction xs with
  | nil => simp [incrementAt]
  | cons x xs ih => simp [incrementAt,ih,Nat.add_assoc]

private theorem increment_gadget (base a offset : ℕ) (c : Fin u → ℕ) :
    incrementAt base a (gadgetRecords offset c) =
      ∑ g, if base+(offset+g.val) = a then c g else 0 := by
  induction u generalizing offset with
  | zero => simp [gadgetRecords,incrementAt]
  | succ u ih =>
    rw [Fin.sum_univ_succ]
    unfold gadgetRecords
    rw [List.ofFn_succ,incrementAt]
    have htail :
        (List.ofFn (fun g : Fin u => (offset+(g.succ).val,c g.succ))) =
          gadgetRecords (offset+1) (fun g => c g.succ) := by
      simp [gadgetRecords,Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
    rw [htail,ih]
    simp [Fin.val_succ,Nat.add_comm,Nat.add_left_comm]

private theorem increment_unary (ls : List (Leaf (Fin h) (Fin u))) (base : ℕ) (i : Fin h) :
    incrementAt base (base+i.val) (ls.filterMap unaryRecord) = powerCounts ls i := by
  classical
  induction ls with
  | nil => simp [incrementAt,powerCounts]
  | cons l ls ih =>
    cases l with
    | check b | scalar b =>
      simpa [unaryRecord,powerCounts,List.filterMap_cons,Leaf.powerEvent] using ih
    | power p j b =>
      cases b <;> by_cases he : p = i <;>
        simp_all [unaryRecord,powerCounts,List.filterMap_cons,Leaf.powerEvent,
          Finsupp.single_apply,incrementAt,Fin.ext_iff]

private theorem increment_unary_outside (ls : List (Leaf (Fin h) (Fin u))) (base a : ℕ) (ha : h ≤ a) :
    incrementAt base (base+a) (ls.filterMap unaryRecord) = 0 := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    cases l with
    | check b | scalar b => simpa [List.filterMap_cons,unaryRecord] using ih
    | power p j b =>
      have he : p.val ≠ a := by omega
      simp [unaryRecord,incrementAt,he,ih]

/-- The external sparse update accumulates precisely the private assignment's
selected binary powers for this parameter. -/
theorem cellRecords_parameter (ls : List (Leaf (Fin h) (Fin u))) (base : ℕ) (p : Fin h) :
    incrementAt base (base+p.val) (cellRecords ls) = powerCounts ls p := by
  classical
  rw [cellRecords,increment_append,increment_unary,increment_gadget]
  have hz (g : Fin u) : h+g.val ≠ p.val := by omega
  simp [hz]

/-- The external update adds the private checker's count for a particular table
position, regardless of the scalar stored in that position. -/
theorem cellRecords_gadget (ls : List (Leaf (Fin h) (Fin u))) (base : ℕ) (g : Fin u) :
    incrementAt base (base+(h+g.val)) (cellRecords ls) = scalarCounts ls g := by
  classical
  rw [cellRecords,increment_append,increment_unary_outside ls base _ (by omega),zero_add,
    increment_gadget]
  simp [← Fin.ext_iff]

/-- Reading a cell's summaries requires one external update per weighted occurrence
and one per fixed gadget position. -/
theorem cellRecords_length (ls : List (Leaf (Fin h) (Fin u))) :
    (cellRecords ls).length = (ls.filterMap unaryRecord).length+u := by
  simp [cellRecords,gadgetRecords]

/-- Several cells with the same owner contribute additively even when their
record coordinates coincide. -/
theorem increment_flatMap {α : Type*} (base a : ℕ) (xs : List α) (records : α → List (ℕ × ℕ)) :
    incrementAt base a (xs.flatMap records) =
      (xs.map fun x => incrementAt base a (records x)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [increment_append,ih]

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
