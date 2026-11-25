import OAI.ThreeFlat.RAM.HistoryBucketEmitter
import OAI.ThreeFlat.RAM.DescriptorExpr

namespace OAI
/-! # Bottom-up aggregation of compact work and pair counts

A two-word task is a destination counter offset and the address of a child
counter. Consecutive even and odd offsets carry work and external-pair count.
The same task body therefore combines both quantities for every child, adding
them to the parent's already initialized local charge.
-/

namespace ThreeFlat.RAM.HistoryChargeScan

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM DescriptorExpr

variable {w r k : ℕ}

/-- Source cursor, destination counter base, exclusive task end, scratch and
unit registers are fixed throughout the scan. -/
def ops (R : Fin 8 ↪ Fin r) : List (Computability.VPVNP.PrimedStackRAM.Op r k) :=
  [.constant (R 7) 1, .read (R 3) (R 0), .binary .add (R 3) (R 1) (R 3),
   .read (R 4) (R 3), .binary .add (R 0) (R 0) (R 7), .read (R 5) (R 0),
   .read (R 6) (R 5), .binary .add (R 4) (R 4) (R 6), .write (R 3) (R 4),
   .binary .add (R 0) (R 0) (R 7)]

def afterRow (m : Memory w) (src base : Word w) : Memory w :=
  let dest := base + m src.val
  let qty := m (m (src+1).val).val
  writeMemory m dest (m dest.val + qty)

set_option maxRecDepth 2048 in
theorem trace_row (R : Fin 8 ↪ Fin r) (pub : Fin k → Word w) (state : Word w)
    (reg : Regs w r) (m : Memory w) :
    ∃ es out, trace pub state (ops R) reg m = some (es,out,afterRow m (reg (R 0)) (reg (R 1))) ∧
      es.length = 10 ∧ out (R 0) = reg (R 0)+1+1 ∧ out (R 1) = reg (R 1) ∧ out (R 2) = reg (R 2) := by
  simp [ops,trace,Computability.VPVNP.PrimedStackRAM.Op.effect,BinaryOp.eval,afterRow,Function.update,R.injective.eq_iff]; first | rfl | exact ⟨rfl,rfl⟩

theorem advance_row {p : ℕ} (R : Fin 8 ↪ Fin r) {M : Machine w p r k} {start stop bad : Fin p}
    (linked : Contains M bad start (ops R) stop) (state : Word w) (reg : Regs w r)
    (priv : Word w → Word w) (m : Memory w) :
    ∃ out, advance M.program 10 ⟨start,state,reg,priv⟩ m =
      some (⟨stop,state,out,priv⟩,afterRow m (reg (R 0)) (reg (R 1))) ∧
      out (R 0) = reg (R 0)+1+1 ∧ out (R 1) = reg (R 1) ∧ out (R 2) = reg (R 2) := by
  obtain ⟨es,out,tr,_,fields⟩ := trace_row R M.publicData state reg m
  exact ⟨out, HistoryBucketEmitter.advance_trace linked state reg out priv m _ es tr,fields⟩

/-- A pair of tasks for each child is emitted by one regular source scan. Its
four words are `2*parent`, `oldBase+2*child`, `2*parent+1`, `oldBase+2*child+1`. -/
def taskWord (k : ℕ) : Term w k 4 :=
  let delta := Term.binary .sub (.result 0) (.result 1)
  let child := Term.binary .div delta (.literal 4)
  let col := Term.binary .mod delta (.literal 4)
  let coord := Term.binary .div col (.literal 2)
  let parent := (Term.binary .add (.result 2) child).load
  let dst := Term.binary .add (Term.binary .mul (.literal 2) parent) coord
  let src := Term.binary .add (Term.binary .add (.result 3) (Term.binary .mul (.literal 2) child)) coord
  Term.select .eq (Term.binary .mod col (.literal 2)) (.literal 0) dst src

def taskValue (m : Memory w) (address start parents old : Word w) : Word w :=
  let delta := address-start
  let child := BinaryOp.eval .div delta 4
  let col := BinaryOp.eval .mod delta 4
  let coord := BinaryOp.eval .div col 2
  if (BinaryOp.eval .mod col 2) = 0 then 2*m (parents+child).val+coord else old+2*child+coord

theorem taskWord_eval (pub : Fin k → Word w) (m : Memory w) (vs : Fin 4 → Word w) :
    (taskWord k).eval pub m vs = taskValue m (vs 0) (vs 1) (vs 2) (vs 3) := by
  simp only [taskWord,Term.eval_select,Term.eval_binary,Term.eval_load,Term.eval_literal,Term.eval,
    Comparison.test,beq_iff_eq,BinaryOp.eval,taskValue]
  split_ifs <;> simp_all

end ThreeFlat.RAM.HistoryChargeScan

end OAI
