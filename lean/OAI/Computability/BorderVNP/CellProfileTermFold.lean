import OAI.Computability.BorderVNP.CellSparseTable
import OAI.Computability.BorderVNP.CellSerializedLength

/-! # The two passes emitting a right fold of Boolean cell terms

Each operand is written at its actual temporary-stack offset in the forward pass.
The terminal literal and one fixed NAND fragment per operand finish the fold.
The identity applies to the framed stream consumed by the private generator.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.TermFold

open CellMacro CellMacro.Generator

/-- The Boolean operator used by a right fold. -/
def join (disj : Bool) : Term → Term → Term := if disj then .or else .and

/-- Bytes following each left operand in the forward pass. -/
def between (depth : ℕ) (disj : Bool) : List Bool :=
  if disj then serialized depth flip else []

/-- Bytes returning from a right operand to its caller. -/
def finish (depth : ℕ) (disj : Bool) : List Bool :=
  if disj then serialized depth flip ++ serialized depth (.fixed .nand)
  else serialized depth (.fixed .nand) ++ serialized depth flip

private theorem emit_join (depth tmp : ℕ) (disj : Bool) (a b : Term) :
    serialized depth ((join disj a b).emit tmp) =
      (serialized depth (a.emit tmp) ++ between depth disj) ++
        serialized depth (b.emit (tmp+1)) ++ finish depth disj := by
  cases disj <;>
    simp only [join, between, finish, Bool.false_eq_true, ↓reduceIte, Term.emit,
      sequence, List.foldr_cons, List.foldr_nil, serialized, wire, records_append,
      records, List.append_nil, List.append_assoc]

private theorem emit_range' (depth tmp start count : ℕ) (disj terminal : Bool) (f : ℕ → Term) :
    serialized depth ((((List.range' start count).map f).foldr (join disj)
      (.lit terminal)).emit (tmp+start)) =
    (List.range' start count).flatMap (fun i =>
      serialized depth ((f i).emit (tmp+i)) ++ between depth disj) ++
    serialized depth (.fixed (.literal terminal)) ++
    (List.range count).flatMap (fun _ => finish depth disj) := by
  induction count generalizing start with
  | zero => simp [Term.emit]
  | succ n ih =>
    rw [List.range'_succ, List.map_cons, List.foldr_cons, emit_join]
    rw [Nat.add_assoc, ih, List.flatMap_cons, List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-- Exact serialization as two flat maps; the depth of the fold does not duplicate
any previously emitted partial word. -/
theorem emit_range (depth tmp count : ℕ) (disj terminal : Bool) (f : ℕ → Term) :
    serialized depth ((((List.range count).map f).foldr (join disj)
      (.lit terminal)).emit tmp) =
    (List.range count).flatMap (fun i =>
      serialized depth ((f i).emit (tmp+i)) ++ between depth disj) ++
    serialized depth (.fixed (.literal terminal)) ++
    (List.range count).flatMap (fun _ => finish depth disj) := by
  simpa only [← List.range_eq_range',Nat.add_zero] using emit_range' depth tmp 0 count disj terminal f

private theorem wordIs_range' (start count j : ℕ) (a : ℕ → NatExpr) :
    wordIs ((List.range' start count).map a) (j >>> start) =
    ((List.range' start count).map (fun i => (Term.wire (a i)).equal (.lit (j.testBit i)))).foldr
      Term.and (.lit (decide (j >>> (start+count) = 0))) := by
  induction count generalizing start with
  | zero => simp [wordIs]
  | succ n ih =>
    simp only [List.range'_succ, List.map_cons, List.foldr_cons, wordIs]
    have hd : (j >>> start)/2 = j >>> (start+1) := by
      rw [Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (j >>> start)]
    rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero, hd, ih]
    rw [show start+1+n = start+(n+1) by omega]

/-- Word equality is the right fold of the actual digit tests. Its terminal bit
rejects any remaining high digits, including when the declared width is zero. -/
theorem wordIs_range (count j : ℕ) (a : ℕ → NatExpr) :
    wordIs ((List.range count).map a) j =
    ((List.range count).map (fun i => (Term.wire (a i)).equal (.lit (j.testBit i)))).foldr
      Term.and (.lit (decide (j.size ≤ count))) := by
  have hz : j >>> count = 0 ↔ j.size ≤ count := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (by positivity), Nat.size_le]
  simpa only [← List.range_eq_range', Nat.shiftRight_zero, Nat.zero_add,hz] using
    wordIs_range' 0 count j a

end CellSparse.Packet.TermFold

end BorderVNP
end Computability
end OAI
