import OAI.Computability.BorderVNP.CellGeneratorWire
import OAI.Computability.BorderVNP.CellSparseCompiled

/-!
# Seeding a cell's actual external assignment bank

The incoming boundary, delivery and subtotal bits occur in address order in the cell's
external bank. A fixed literal command for each bit, emitted in reverse order, places
that bank in precisely the state expected by the private assignment checker. This
initialization makes no nondeterministic choices and contributes positive sign.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactMachine

open CellSparse CellMacro CellMacro.Generator

/-- Emit literal pushes in the specified chronological order, then enter the body. -/
def pushLiterals : List Bool → Stmt → Stmt
  | [], s => s
  | b :: bs, s => .seq (.fixed (.literal b)) (pushLiterals bs s)

/-- Install an address-ordered external stack before the private-cell body starts. -/
def withExternal (external : List Bool) (body : Stmt) : Stmt := pushLiterals external.reverse body

/-- The physical command encoding of one fixed literal. Its only varying digit is at offset ten. -/
def literalRecord (b : Bool) : List Bool :=
  [true,false,false,false,false,false,false,false,false,false,b,true]

/-- Chronological compact literal records supplied to the private generator by the outer team. -/
def externalRecords (external : List Bool) : List Bool := external.reverse.flatMap literalRecord

private theorem serialized_push (d : ℕ) (bits : List Bool) (s : Stmt) :
    serialized d (pushLiterals bits s) = bits.flatMap literalRecord ++ serialized d s := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    change literalRecord b ++ serialized d (pushLiterals bits s) = _
    rw [ih, List.flatMap_cons, List.append_assoc]

/-- Serialization stores the private directory body once after the ordered external records. -/
theorem serialized_withExternal (d : ℕ) (external : List Bool) (s : Stmt) :
    serialized d (withExternal external s) = externalRecords external ++ serialized d s :=
  serialized_push ..

private theorem length_literalRecords (bits : List Bool) :
    (bits.flatMap literalRecord).length = 12*bits.length := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons, Nat.mul_succ]
    exact Nat.add_comm 12 _

/-- Adding one external assignment bit costs twelve bits in the compact descriptor. -/
theorem length_externalRecords (external : List Bool) : (externalRecords external).length = 12*external.length := by
  rw [externalRecords, length_literalRecords, List.length_reverse]

/-- The actual expansion emits one chronological literal instruction per specified bit. -/
theorem expand_push (bits : List Bool) (s : Stmt) (env : List ℕ) :
    (pushLiterals bits s).expand env = bits.map Op.literal ++ s.expand env := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [pushLiterals,Stmt.expand,ih]

private theorem value_literal_stack (bits : List Bool) (ops : List Op) (f : Flags) (bank : List Bool) :
    value (bits.map Op.literal ++ ops) f bank = value ops f (bits.reverse ++ bank) := by
  induction bits generalizing bank with
  | nil => rfl
  | cons b bits ih => simp [value, Op.effect, ih]

/-- The literal records reconstruct the specified bank without changing either Boolean flag. -/
theorem value_withExternal (external : List Bool) (s : Stmt) (env : List ℕ) (f : Flags) :
    value ((withExternal external s).expand env) f [] = value (s.expand env) f external := by
  rw [withExternal,expand_push,value_literal_stack,List.reverse_reverse,List.append_nil]

/-- The actual seeded sparse cell computes the sum over its private assignments, retaining
the exact supplied boundary values at their original offsets. -/
theorem value_external_directory (D : Directory) (privateWires : ℕ) (external : List Bool) (env : List ℕ) :
    value ((withExternal external (D.program privateWires)).expand env) ⟨true,false⟩ [] =
      ∑ x : Fin privateWires → Bool, D.weight (lookup (List.ofFn x ++ external)) := by
  rw [value_withExternal, D.value_program]

private theorem fits_push (bits : List Bool) (s : Stmt) (d h : ℕ) :
    (pushLiterals bits s).FitsDepth d h ↔ s.FitsDepth d h := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [pushLiterals,Stmt.FitsDepth,ih]

/-- Literal commands consume no address or lexical depth of the fixed interpreter. -/
theorem fits_withExternal (external : List Bool) (s : Stmt) (d h : ℕ) :
    (withExternal external s).FitsDepth d h ↔ s.FitsDepth d h := fits_push ..

private theorem ticks_push (bits : List Bool) (s : Stmt) (cl : Clocks) (d : ℕ) (env : List ℕ) :
    scanCost (jobs cl d (pushLiterals bits s) env) = 104*bits.length + scanCost (jobs cl d s env) := by
  induction bits with
  | nil => simp [pushLiterals]
  | cons b bits ih =>
    change 104 + ((jobs cl d (pushLiterals bits s) env).map _).sum + 1 = _
    change _ = 104*(bits.length+1) + _
    rw [Nat.mul_succ]
    change ((jobs cl d (pushLiterals bits s) env).map _).sum + 1 = _ at ih
    omega

/-- A literal row costs exactly 104 elementary steps in the generator's scan allowance. -/
theorem scanCost_withExternal (external : List Bool) (s : Stmt) (cl : Clocks) (d : ℕ) (env : List ℕ) :
    scanCost (jobs cl d (withExternal external s) env) = 104*external.length + scanCost (jobs cl d s env) := by
  rw [withExternal,ticks_push,List.length_reverse]

private theorem byte_push (bits : List Bool) (s : Stmt) (env : List ℕ) :
    (stream ((pushLiterals bits s).expand env)).length =
        2*bits.length + (stream (s.expand env)).length ∧
      budget ((pushLiterals bits s).expand env) = 3*bits.length + budget (s.expand env) := by
  induction bits with
  | nil => simp [pushLiterals]
  | cons b bits ih =>
    obtain ⟨x,y⟩ := ih
    change ((Op.literal b).bits ++ stream ((pushLiterals bits s).expand env)).length = _ ∧
      (3+(((pushLiterals bits s).expand env).map Op.ticks).sum)+2 = _
    rw [List.length_append, show (Op.literal b).bits.length = 2 from rfl, List.length_cons]
    change (((pushLiterals bits s).expand env).map Op.ticks).sum+2 = _ at y
    omega

/-- Two emitted bits and three interpreter ticks suffice for each supplied external bit. -/
theorem byteCosts_withExternal (external : List Bool) (s : Stmt) (env : List ℕ) :
    (stream ((withExternal external s).expand env)).length =
        2*external.length + (stream (s.expand env)).length ∧
      budget ((withExternal external s).expand env) = 3*external.length + budget (s.expand env) := by
  simpa only [withExternal, List.length_reverse] using byte_push external.reverse s env

end RoutingISA.CompactMachine

end BorderVNP
end Computability
end OAI
