import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.NormNum
import OAI.ThreeFlat.RAM.ContinuationLink
import OAI.ThreeFlat.RAM.HistoryBucketEmitter

namespace OAI
/-! # Compact chronological node and kernel tables shared by navigation and preparation -/

namespace ThreeFlat.RAM.HistoryNodeDirectory

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink Computability.VPVNP.PrimedStackRAM
open scoped Fin.CommRing

/-- Compact stage tag stored in each node, stage and kernel descriptor. -/
inductive Kind where | initial | shrink | refresh | identity deriving DecidableEq

def Kind.tag : Kind → ℕ | .initial => 0 | .shrink => 1 | .refresh => 2 | .identity => 3

structure RootHeader (α : Type*) where
  firstFinal : α
  nodeBase : α
  childBase : α

structure Stage (α : Type*) where
  first : α
  count : α
  kind : α
  info : α

structure Node (α : Type*) where
  kind : α
  parent : α
  ordinal : α
  childPtr : α
  childCount : α
  kernelPtr : α
  incidentPtr : α
  externalCount : α

structure Kernel (α : Type*) where
  stagePtr : α
  site : α
  kind : α
  motifCount : α
  motifBase : α

structure Motif (α : Type*) where
  key : α
  histogram : α
  demandShape : α
  tiles : α
  absorbedMask : α
  partyMask : α

structure Half (α : Type*) where
  slot : α
  side : α
  width : α
  offset : α

def Node.words {α : Type*} (q : Node α) : Fin 8 → α :=
  ![q.kind,q.parent,q.ordinal,q.childPtr,q.childCount,q.kernelPtr,q.incidentPtr,q.externalCount]

def Stage.words {α : Type*} (q : Stage α) : Fin 4 → α := ![q.first,q.count,q.kind,q.info]

def RootHeader.words {α : Type*} (q : RootHeader α) : Fin 3 → α := ![q.firstFinal,q.nodeBase,q.childBase]

def Kernel.words {α : Type*} (q : Kernel α) : Fin 5 → α := ![q.stagePtr,q.site,q.kind,q.motifCount,q.motifBase]

def Motif.words {α : Type*} (q : Motif α) : Fin 6 → α := ![q.key,q.histogram,q.demandShape,q.tiles,q.absorbedMask,q.partyMask]

def Half.words {α : Type*} (q : Half α) : Fin 4 → α := ![q.slot,q.side,q.width,q.offset]

/-- Every predecessor precedes its physical parent, and the terminal nodes
are one consecutive suffix of global site IDs. -/
structure Chronology (n : ℕ) where
  firstFinal : ℕ
  bounded : firstFinal ≤ n
  parent : Fin n → Fin n
  later : ∀ i, i.val < firstFinal → i.val < (parent i).val

def Chronology.root {n : ℕ} (A : Chronology n) (i : Fin n) : ℕ :=
  if _old : i.val < A.firstFinal then A.root (A.parent i) else i.val-A.firstFinal
termination_by n-i.val
decreasing_by have h := A.later i _old; have _p := (A.parent i).isLt; omega

theorem Chronology.root_lt {n : ℕ} (A : Chronology n) (i : Fin n) : A.root i < n-A.firstFinal := by
  induction i using Chronology.root.induct A with
  | case1 i test ih => rw [Chronology.root,dite_eq_left test]; exact ih
  | case2 i test => rw [Chronology.root,dite_eq_right test]; have := i.isLt; omega

/-- Register zero is the output cursor, registers one through eight hold
all compact fields, and register nine is a scratch constant. -/
def nodeOps (r k : ℕ) (R : Fin 10 ↪ Fin r) : List (Op r k) :=
  .constant (R 9) 1 :: (List.ofFn fun i : Fin 8 =>
    [.write (R 0) (R (i.succ.castAdd 1)),.binary .add (R 0) (R 0) (R 9)]).flatten

@[simp] theorem nodeOps_length {r k : ℕ} (R : Fin 10 ↪ Fin r) : (nodeOps r k R).length = 17 := rfl

def nodeWord {w : ℕ} (r : Node (Word w)) (i : Fin 8) := r.words i

def emitWords {w : ℕ} (src : Fin 8 → Word w) (cursor : Word w) (m : Memory w) : Memory w :=
  (List.ofFn fun i : Fin 8 => (cursor+(i.val : Word w),src i)).foldl (fun z kv => writeMemory z kv.1 kv.2) m

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- All eight writes, including the last cursor update, are literal RAM operations. -/
theorem node_trace {w r k : ℕ} (R : Fin 10 ↪ Fin r) (pub : Fin k → Word w) (state : Word w)
    (reg : Regs w r) (m : Memory w) :
    ∃ es out, trace pub state (nodeOps r k R) reg m = some (es,out,emitWords (fun i => reg (R (i.succ.castAdd 1))) (reg (R 0)) m) ∧
      out (R 0) = reg (R 0)+8 := by
  simp [nodeOps,emitWords,List.ofFn_succ,trace,Op.effect,BinaryOp.eval,Function.update,R.injective.eq_iff,add_assoc]; norm_num

end ThreeFlat.RAM.HistoryNodeDirectory

end OAI
