import OAI.ThreeFlat.RAM.TickChunkPredicate
import OAI.ThreeFlat.RAM.TickChunkRule
import OAI.ThreeFlat.RAM.TickRequestStream

namespace OAI
/-! # The program and native cost of checking a physical external chunk -/

namespace ThreeFlat.RAM.TickChunkCheck

open Computability.VPVNP.BurstRAM DescriptorExpr Diagonal.TickAuxiliary Diagonal.TickGroupIntervals TickIntervalCursor
open scoped Fin.CommRing

def rules (groupScan : Bool) (L : Layout) (es : List Interval) (op np : ℕ → Bool) (i : ℕ) : Rule :=
  if groupScan then TickChunkRule.rule (codeAt L es i) op np else .same

def ruleExpr (w k : ℕ) (groupScan : Bool) (L : Layout) (oldPtr newPtr : ℕ) : Term w k 1 :=
  if groupScan then TickChunkRule.atRow w k L.mapBase oldPtr newPtr else .literal 1

theorem ruleExpr_binds (w k : ℕ) (groupScan : Bool) (L : Layout) (oldPtr newPtr : ℕ) :
    (ruleExpr w k groupScan L oldPtr newPtr).binds ≤ 40 := by
  cases groupScan with
  | false => simp [ruleExpr,Term.literal,Term.binds]
  | true =>
    have bound := TickChunkRule.lookup_binds w k
    simp [ruleExpr,TickChunkRule.atRow,Term.load,Term.binary,Term.literal,Term.binds,Fin.sum_univ_succ]; omega

theorem cost_le (w k start : ℕ) (groupScan : Bool) (L : Layout) (oldPtr newPtr : ℕ) :
    14+8*chunkSize L*((TickRequestStream.program start (ruleExpr w k groupScan L oldPtr newPtr)).steps+3)+
      chunkSize L*122 ≤ 14+4314*chunkSize L := by
  have hg := TickRequestStream.program_binds start (ruleExpr w k groupScan L oldPtr newPtr)
  have hr := ruleExpr_binds w k groupScan L oldPtr newPtr
  have term : (TickRequestStream.program start (ruleExpr w k groupScan L oldPtr newPtr)).steps+3 ≤ 524 := by
    rw [Term.steps_eq]
    omega
  have := Nat.mul_le_mul_left (8*chunkSize L) term
  omega


end ThreeFlat.RAM.TickChunkCheck

end OAI
