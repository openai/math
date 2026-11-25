import OAI.LinearAlgebra.SpectralBooks.SignedProgramPadding
import Mathlib.Data.List.OfFn

/-! # Fixed field positions for the signed program prefix

Every padded row and transition has fixed field positions. Inactive fields
emit the empty list. Active fields emit the manuscript encoding's unary word.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram

open SignedMachine

def symbolCode : Symbol → ℕ
  | .blank => 0 | .zero => 1 | .one => 2

def directionCode : Direction → ℕ
  | .left => 0 | .stay => 1 | .right => 2

def outputCode : Output → ℕ
  | .zero => 0 | .pos => 1 | .neg => 2

def emit (fields : List (Option ℕ)) : List Bool :=
  fields.flatMap fun f ↦ f.elim [] ProgramCode.unary

@[simp] theorem emit_append (a b : List (Option ℕ)) : emit (a ++ b) = emit a ++ emit b := by
  simp [emit]

@[simp] theorem emit_nil : emit [] = [] := rfl

@[simp] theorem emit_cons (i : ℕ) (a : List (Option ℕ)) :
    emit (some i :: a) = ProgramCode.unary i ++ emit a := rfl

/-- Suppress a block without shifting its position in the schedule. -/
def mask (active : Bool) (fields : List (Option ℕ)) : List (Option ℕ) :=
  if active then fields else List.replicate fields.length none

@[simp] theorem length_mask (active : Bool) (fs : List (Option ℕ)) :
    (mask active fs).length = fs.length := by cases active <;> simp [mask]

@[simp] theorem emit_mask (b : Bool) (fs : List (Option ℕ)) :
    emit (mask b fs) = if b then emit fs else [] := by
  cases b <;> simp [mask,emit]

/-- Emit a fixed block for each possible row or tape, including padding. -/
def blocks {n : ℕ} (count : Fin (n+1)) (f : Fin n → List (Option ℕ)) : List (Option ℕ) :=
  (List.ofFn fun i ↦ mask (decide (i.val < count.val)) (f i)).flatten

theorem length_blocks {n c : ℕ} (k : Fin (n+1)) (f : Fin n → List (Option ℕ))
    (hc : ∀ i, (f i).length = c) : (blocks k f).length = n*c := by
  simp [blocks,List.length_flatten,List.map_ofFn,Function.comp_def,hc,List.ofFn_const]

private theorem emit_flatten (ls : List (List (Option ℕ))) :
    emit ls.flatten = (ls.map emit).flatten := by
  induction ls with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem emit_blocks {n : ℕ} (k : Fin (n+1)) (f : Fin n → List (Option ℕ)) :
    emit (blocks k f) = ((activeList k f).map emit).flatten := by
  obtain ⟨k,hk⟩ := k
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt_succ hk)
  rw [blocks, List.ofFn_add]
  simp [List.flatten_append, emit_flatten, activeList, List.map_ofFn,
    Function.comp_def, emit_mask, List.ofFn_const]

/-- Slots of one padded transition. -/
def Move.fields {n : ℕ} (m : Move n) (tapes : Fin (n+1)) : List (Option ℕ) :=
  [some m.state.val, some (directionCode m.inputMove)] ++
    blocks tapes (fun i ↦ [some (symbolCode (m.work i).1), some (directionCode (m.work i).2)])

/-- Slots of a padded rule. All three action formats share this layout. -/
def Row.fields {n : ℕ} (r : Row n) (tapes : Fin (n+1)) : List (Option ℕ) :=
  [some r.state.val, some (symbolCode r.input)] ++
    blocks tapes (fun i ↦ [some (symbolCode (r.reads i))]) ++
    [some r.kind.val] ++ mask (decide (r.kind = 0)) [some (outputCode r.out)] ++
    mask (decide (r.kind ≠ 0)) ((r.next false).fields tapes) ++
    mask (decide (r.kind = 2)) ((r.next true).fields tapes)

def Table.bodyFields {n : ℕ} (t : Table n) : List (Option ℕ) :=
  [some t.tapes.val, some t.rows.val] ++ blocks t.rows (fun i ↦ (t.row i).fields t.tapes)

def Table.fields {n : ℕ} (t : Table n) (frame : ℕ) : List (Option ℕ) :=
  some frame :: t.bodyFields

theorem Move.length_fields {n : ℕ} (m : Move n) (k : Fin (n+1)) :
    (m.fields k).length = 2+2*n := by
  simp [Move.fields, length_blocks (c := 2) k (fun i ↦ [some (symbolCode (m.work i).1), some (directionCode (m.work i).2)]) (fun _ ↦ rfl), Nat.mul_comm]
  omega

theorem Row.length_fields {n : ℕ} (r : Row n) (k : Fin (n+1)) :
    (r.fields k).length = 8+5*n := by
  simp [Row.fields, length_blocks (c := 1) k (fun i ↦ [some (symbolCode (r.reads i))]) (fun _ ↦ rfl), Move.length_fields]
  omega

theorem Table.length_fields {n : ℕ} (t : Table n) (frame : ℕ) :
    (t.fields frame).length = 3+n*(8+5*n) := by
  simp [Table.fields, Table.bodyFields, length_blocks _ _ (fun _ ↦ Row.length_fields ..)]
  omega

end SignedProgram

namespace ProgramCode

open SignedMachine SignedProgram
open private symbolBits directionBits outputBits moveBits transitionBits actionBits ruleBits bodyBits from
  OAI.LinearAlgebra.SpectralBooks.SignedWitness

private theorem symbolBits_eq (s : Symbol) : symbolBits s = unary (symbolCode s) := by cases s <;> rfl
private theorem directionBits_eq (d : Direction) : directionBits d = unary (directionCode d) := by cases d <;> rfl
private theorem outputBits_eq (o : Output) : outputBits o = unary (outputCode o) := by cases o <;> rfl

private theorem active_flatMap {α β : Type*} {n : ℕ} (k : Fin (n+1)) (f : Fin n → α) (g : α → List β) :
    (activeList k f).flatMap g = (activeList k (fun i ↦ g (f i))).flatten := by
  have H (ls : List α) : (ls.map g).flatten = ls.flatMap g := by
    induction ls <;> simp [*]
  rw [← H, activeList, List.map_ofFn]
  rfl

private theorem active_map {α β : Type*} {n : ℕ} (k : Fin (n+1)) (f : Fin n → α) (g : α → β) :
    (activeList k f).map g = activeList k (fun i ↦ g (f i)) := by
  rw [activeList, List.map_ofFn]
  rfl

private theorem emit_move {n : ℕ} (m : Move n) (k : Fin (n+1)) :
    emit (m.fields k) = transitionBits (m.transition k) := by
  simp [Move.fields, emit_blocks, Move.transition, transitionBits, directionBits_eq,
    active_map, active_flatMap,moveBits,symbolBits_eq]

private theorem emit_row {n : ℕ} (r : Row n) (k : Fin (n+1)) :
    emit (r.fields k) = ruleBits (r.rule k) := by
  cases r with
  | mk s y ys tag sign moves =>
    fin_cases tag <;>
      simp [Row.fields, emit_blocks, Row.rule, Row.action, ruleBits, actionBits, symbolBits_eq,
        outputBits_eq, active_map, active_flatMap, emit_move, List.append_assoc]

theorem emit_bodyFields {n : ℕ} (t : Table n) : emit t.bodyFields = bodyBits t.program := by
  simp only [Table.bodyFields, Table.program, bodyBits, emit_append, emit_cons, emit_nil,
    List.append_nil, emit_blocks, active_map, active_flatMap, emit_row]
  simp [activeList]

/-- The emitted fields match the entire self-delimiting code when the frame
equals the emitted body length. -/
theorem emit_fields_eq_encode {n : ℕ} (t : Table n) :
    emit (t.fields (emit t.bodyFields).length) = encode t.program := by
  rw [Table.fields, emit_cons, emit_bodyFields, encode]

end ProgramCode

end SpectralBooks
end LinearAlgebra
end OAI
