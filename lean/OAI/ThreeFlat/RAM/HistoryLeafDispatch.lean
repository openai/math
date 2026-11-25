import OAI.ThreeFlat.RAM.HistoryStaticArchive
import OAI.ThreeFlat.RAM.StableCompactROMProgram

namespace OAI
/-! # The three numerical descriptor formats at selected leaves -/

namespace ThreeFlat.RAM.HistoryLeafDispatch

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr
open scoped Fin.CommRing

variable {w k : ℕ}

inductive Kind where | first | fixed | compact deriving DecidableEq

def Kind.tag : Kind → ℕ | .first => 0 | .fixed => 1 | .compact => 2

/-- A selected leaf has five header words. Four contain `[kind,a,b,c]`,
and the fifth is the destination's starting address. The three operands are
`[lane,stage,0]`, `[archive,stride,table]`, or `[2^m,n,page]`. -/
structure Input (w : ℕ) where
  kind : Word w
  a : Word w
  b : Word w
  c : Word w
  dest : Word w

def Input.words (e : Input w) : Fin 5 → Word w := ![e.kind,e.a,e.b,e.c,e.dest]

private def get (base : Fin k) (j : ℕ) : Term w k 1 :=
  (Term.binary .add (.parameter base) (.literal (j : Word w))).load

def memory (base : Word w) (m : Memory w) : Input w :=
  let rd (i : ℕ) := m (base+(i:Word w)).val
  ⟨rd 0,rd 1,rd 2,rd 3,rd 4⟩

/-- Every physical leaf uses the same scanner. `initial` is the uniform trace
row decoder on `[row,column,lane,stage]`. The compacting and fixed cases
use their actual native ROM decoders. -/
def term (initial : Term w k 4) (base : Fin k) : Term w k 1 :=
  let key := Term.binary .sub (.result 0) (get base 4)
  let a := get base 1; let b := get base 2; let c := get base 3
  let row := Term.binary .div key (.literal 4); let col := Term.binary .mod key (.literal 4)
  let orig := initial.instantiate ![row,col,a,b]
  let lut := (HistoryStaticArchive.program w k).instantiate ![a,b,c,Term.binary .add (.literal 2) key]
  let comp := StableCompactROMProgram.program.instantiate ![key,a,b,c]
  Term.select .eq (get base 0) (.literal 0) orig (Term.select .eq (get base 0) (.literal 1) lut comp)

def readWord (initial : Term w k 4) (pub : Fin k → Word w) (mem : Memory w) (e : Input w)
    (ptr : Word w) :=
  let key := ptr-e.dest
  if e.kind=0 then initial.eval pub mem ![BinaryOp.eval .div key 4,BinaryOp.eval .mod key 4,e.a,e.b]
  else if e.kind=1 then (HistoryStaticArchive.program w k).eval pub mem ![e.a,e.b,e.c,2+key]
  else StableCompactROMProgram.program.eval pub mem ![key,e.a,e.b,e.c]

private theorem four (a b c d : Term w k 1) (pub : Fin k → Word w) (mem : Memory w) (x : Fin 1 → Word w) :
    (fun i => (![a,b,c,d] i).eval pub mem x) = ![a.eval pub mem x,b.eval pub mem x,c.eval pub mem x,d.eval pub mem x] := by
  funext i
  fin_cases i <;> rfl

set_option maxRecDepth 4096 in
theorem term_eval (initial : Term w k 4) (base : Fin k) (pub : Fin k → Word w) (mem : Memory w) (vs : Fin 1 → Word w) :
    (term initial base).eval pub mem vs = readWord initial pub mem (memory (pub base) mem) (vs 0) := by
  simp only [term,readWord,Term.eval_select,Term.eval_literal,Term.eval_instantiate]
  simp only [four]
  simp [get,memory,Term.eval,BinaryOp.eval,Comparison.test]

set_option maxRecDepth 4096 in
theorem binds_le (initial : Term w k 4) (base : Fin k) : (term initial base).binds ≤ initial.binds+160 := by
  have h := StableCompactROMProgram.program_binds (w:=w) (k:=k)
  simp [term,get,Term.select,Term.binary,Term.literal,Term.parameter,Term.load,Term.binds,Fin.sum_univ_succ,HistoryStaticArchive.program_binds]; omega

end ThreeFlat.RAM.HistoryLeafDispatch

end OAI
