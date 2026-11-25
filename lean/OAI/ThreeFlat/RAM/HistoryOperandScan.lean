import OAI.ThreeFlat.RAM.HistoryBatchProgram
import OAI.ThreeFlat.RAM.HistoryPartyGather
import OAI.ThreeFlat.RAM.HistoryMotifMaps
import OAI.ThreeFlat.RAM.HeaderScan

namespace OAI
/-! # Mounting the numerical fields of selected range generators in scratch -/

namespace ThreeFlat.RAM.HistoryOperandScan

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr
open scoped Fin.CommRing

variable {w k a : ℕ}

/-- The selected kernel controller writes `[outputBase,outputLength,args…]`
into its private header. Only this fixed number of words changes between
ranges. `row` and `column` are derived from the current absolute cursor. -/
inductive Operand where | row | column | header (i : ℕ) deriving DecidableEq

def field (base : Fin k) (i : ℕ) : Term w k 1 :=
  (.binary .add (.parameter base) (.literal (i : Word w)) : Term w k 1).load

def operand (base : Fin k) (stride : ℕ) : Operand → Term w k 1
  | .header i => field base i
  | .row => .binary .div (.binary .sub (.result 0) (field base 0)) (.literal (stride : Word w))
  | .column => .binary .mod (.binary .sub (.result 0) (field base 0)) (.literal (stride : Word w))

def program (e : Term w k a) (base : Fin k) (stride : ℕ) (op : Fin a → Operand) :=
  e.instantiate (fun j => operand base stride (op j))

def input (mem : Memory w) (base addr : Word w) (stride : ℕ) : Operand → Word w
  | .header i => mem (base+(i : Word w)).val
  | .row => BinaryOp.eval .div (addr-mem base.val) (stride : Word w)
  | .column => BinaryOp.eval .mod (addr-mem base.val) (stride : Word w)

theorem eval (e : Term w k a) (base : Fin k) (stride : ℕ) (op : Fin a → Operand)
    (data : Fin k → Word w) (mem : Memory w) (vs : Fin 1 → Word w) :
    (program e base stride op).eval data mem vs = e.eval data mem (fun j => input mem (data base) (vs 0) stride (op j)) := by
  rw [program,Term.eval_instantiate]
  apply congrArg _
  funext j
  cases op j <;> simp [operand,input,field,Term.eval,BinaryOp.eval]

theorem binds_le (e : Term w k a) (base : Fin k) (stride : ℕ) (op : Fin a → Operand) :
    (program e base stride op).binds ≤ e.binds+7*a := by
  rw [program,Term.binds_instantiate]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _ : Fin a, 7 := Finset.sum_le_sum fun j _ => by cases op j <;> simp [operand,field,Term.binary,Term.load,Term.literal,Term.parameter,Term.binds]
    _ = _ := by simp [Nat.mul_comm]

/-- Only the five task columns consumed by HistoryCommandTable are emitted.
Rows carry child ordinal, the physical data give both leaf sizes. -/
def batchOperands : Fin 14 → Operand :=
  ![.row,.header 2,.header 3,.header 4,.header 5,.header 6,.header 7,.header 8,.header 9,
    .header 10,.header 11,.header 12,.header 13,.column]

def batches (w : ℕ) := program (HistoryBatchProgram.program w) (0 : Fin 1) 5 batchOperands

/-- The party map has a single output word per public bit. -/
def partyOperands : Fin 10 → Operand := ![.row,.header 2,.header 3,.header 4,.header 5,.header 6,.header 7,.header 8,.header 9,.header 10]

def party (w : ℕ) := program (HistoryPartyGather.program w) (0 : Fin 1) 1 partyOperands

/-- One child pin-map run holds constant kind and component/copy ordinal. -/
def motifOperands : Fin 9 → Operand := ![.header 2,.row,.header 3,.header 4,.header 5,.header 6,.header 7,.header 8,.header 9]

def motif (w : ℕ) := program (HistoryMotifMaps.program w) (0 : Fin 1) 1 motifOperands

theorem bounds (w : ℕ) : (batches w).binds≤298 ∧ (party w).binds≤1070 ∧ (motif w).binds≤363 := by
  refine ⟨(binds_le ..).trans ?_,(binds_le ..).trans ?_,(binds_le ..).trans ?_⟩
  · have := HistoryBatchProgram.program_binds w; omega
  · have := HistoryPartyGather.binds w; omega
  · have := HistoryMotifMaps.binds w; omega

end ThreeFlat.RAM.HistoryOperandScan

end OAI
