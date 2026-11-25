import Mathlib.Tactic.FinCases
import OAI.ThreeFlat.RAM.TickBitRelation
import OAI.ThreeFlat.RAM.LiteralTable
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Native row words of a padded auxiliary-bit check

The sixty-four literal entries depend only on the eight bit relations.
Address bits are supplied through the index register at run time.
-/

namespace ThreeFlat.RAM.TickAuxRequestWord
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr Diagonal.TickAuxiliary TickBitRelation ChunkRequests
open scoped Fin.CommRing

def decode : ℕ → Rule
  | 1 => .same | 2 => .oldZero | 3 => .newZero | 4 => .bothZero
  | 5 => .zeroOne | 6 => .oneZero | 7 => .bothOne | _ => .any

def slot (d : Fin 8) : Fin 2 := ⟨d.val/4, by omega⟩
def index (d : Fin 8) : Fin 4 := ⟨d.val%4, Nat.mod_lt _ (by decide)⟩

def columns {w : ℕ} (r : Request w) : Fin 4 → Word w := ![r.chunk, r.mode, r.offset, r.expected]

/-- Static entries in every column except the bit address. -/
private def entry (v : ℕ) : ℕ :=
  let d : Fin 8 := ⟨v%8,Nat.mod_lt _ (by decide)⟩
  match request (decode (v/8)) (slot d) with
  | none => if index d = 0 then 1 else 0
  | some (mode,expected) => if index d = 1 then mode else if index d = 3 then expected else 0

private theorem tag_lt (r : Rule) : r.tag < 8 := by cases r <;> decide

private theorem entry_spec {w : ℕ} (r : Rule) (off : Word w) (d : Fin 8) :
    (if d.val%4 = 2 then off else (entry (8*r.tag+d.val) : Word w)) =
      columns (paddedRequest r (slot d) off) (index d) := by
  cases r <;> fin_cases d <;> rfl

/-- Register zero is the rule tag, register one the offset, and register two
the column among the eight words used for that bit. -/
def program (w k : ℕ) : Term w k 3 :=
  let d : Term w k 3 := .result 2
  let code := Term.binary .add (Term.binary .mul (.literal 8) (.result 0)) d
  .select .eq (.binary .mod d (.literal 4)) (.literal 2) (.result 1)
    (LiteralTable.atIndex (fun j => (entry j : Word w)) 64 code)

theorem program_binds (w k : ℕ) : (program w k).binds ≤ 205 := by
  simp [program, Term.select, Term.binary, Term.literal, Term.binds]

theorem program_eval {w k : ℕ} (fit : 64 ≤ 2^w) (r : Rule) (off : Word w) (d : Fin 8)
    (par : Fin k → Word w) (mem : Memory w) (v : Fin 3 → Word w)
    (hr : v 0 = (r.tag : Word w)) (ho : v 1 = off) (hd : v 2 = (d.val : Word w)) :
    (program w k).eval par mem v = columns (paddedRequest r (slot d) off) (index d) := by
  let e : Term w k 3 := .binary .add (.binary .mul (.literal 8) (.result 0)) (.result 2)
  have ht : 8*r.tag+d.val < 64 := by have := tag_lt r; have := d.isLt; omega
  have hvalue : e.eval par mem v = ((8*r.tag+d.val : ℕ) : Word w) := by
    simp [e, hr, hd, BinaryOp.eval, Term.eval]
  have table := LiteralTable.atIndex_eval (fun j => (entry j : Word w)) 64 _ ht fit par mem v e hvalue
  simp only [program, Term.eval_select, Term.eval_binary, Term.eval_literal, Term.eval, ho, hd]
  change (if Comparison.eq.test (BinaryOp.mod.eval (d.val : Word w) 4) 2 then off else
    (LiteralTable.atIndex (fun j => (entry j : Word w)) 64 e).eval par mem v) = _
  rw [table, ← entry_spec r off d]
  have fd : d.val < 2^w := by have := d.isLt; omega
  have h4 : (4 : ℕ) % 2^w = 4 := Nat.mod_eq_of_lt (by omega)
  have h2 : (2 : ℕ) % 2^w = 2 := Nat.mod_eq_of_lt (by omega)
  have hh : d.val%4 < 2^w := by have := Nat.mod_lt d.val (by decide : 0<4); omega
  have test : Comparison.eq.test (BinaryOp.mod.eval (d.val : Word w) 4) 2 ↔ d.val%4 = 2 := by
    simp only [Comparison.test,beq_iff_eq]
    change (Fin.ofNat (2^w) (((d.val : Word w).val) % (4 : Word w).val) = (2 : Word w)) ↔ _
    rw [Fin.ext_iff]
    simp [Fin.val_cast_of_lt fd, h4,h2,Nat.mod_eq_of_lt hh]
  simp only [test]

end ThreeFlat.RAM.TickAuxRequestWord

end OAI
