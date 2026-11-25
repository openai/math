import OAI.Hierarchy.FactorThresholds
import OAI.ThreeFlat.RAM.OrdinalOpLoop

namespace OAI
/-! # Native word scans for geometric classes and round-robin ticks -/

namespace Hierarchy.FactorBucketRAM

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

variable {w r k : ℕ}

/-- Public words for each ordinal loop. The first word is that loop's number of
iterations. The three passes share table addresses and radices. -/
abbrev Parameters (w : ℕ) := Fin 12 → Word w

def parameters (w limit steps d radix ticks resources thresholds digits keys counts owner : ℕ) :
    Parameters w :=
  ![limit,steps,d,radix,ticks,resources,thresholds,digits,keys,counts,owner,0]

/-- One threshold entry is tested against one original resource word. -/
def digitStep (v : Parameters w) (i : Word w) (m : Memory w) : Memory w :=
  let row := BinaryOp.div.eval i (v 1)
  let col := BinaryOp.mod.eval i (v 1)
  let x := m (v 5 + row).val
  let entry := m (v 6 + col).val
  let dst := v 7 + row
  let old := m dst.val * (BinaryOp.div.eval col col)
  let ratio := BinaryOp.div.eval x entry
  let flag := BinaryOp.div.eval ratio ratio
  writeMemory m dst (old + ((col+1)-old)*flag)

/-- The high-order digit is read first. Folding all digits therefore agrees
with the little-endian coordinate formula of finFunctionFinEquiv. -/
def keyStep (v : Parameters w) (i : Word w) (m : Memory w) : Memory w :=
  let row := BinaryOp.div.eval i (v 2)
  let col := BinaryOp.mod.eval i (v 2)
  let digit := m (v 7 + (row*v 2 + ((v 2-1)-col))).val
  let dst := v 8 + row
  let old := m dst.val * (BinaryOp.div.eval col col)
  writeMemory m dst (old*v 3+digit)

/-- Process factors in their original order, using one mutable count for each
encoded resource tuple. Each row emits one original-factor-to-tick address. -/
def ownerStep (v : Parameters w) (i : Word w) (m : Memory w) : Memory w :=
  let key := m (v 8+i).val
  let ptr := v 9+key
  let old := m ptr.val
  writeMemory (writeMemory m ptr (old+1)) (v 10+i) (BinaryOp.mod.eval old (v 4))

def digitOps : List (Op 14 12) :=
  [.publicWord 2 1, .binary .div 3 0 2, .binary .mod 4 0 2,
   .publicWord 5 5, .binary .add 5 5 3, .read 6 5,
   .publicWord 5 6, .binary .add 5 5 4, .read 7 5,
   .publicWord 5 7, .binary .add 5 5 3, .read 8 5,
   .binary .div 9 4 4, .binary .mul 8 8 9,
   .binary .div 9 6 7, .binary .div 9 9 9,
   .constant 10 1, .binary .add 11 4 10, .binary .sub 11 11 8,
   .binary .mul 11 11 9, .binary .add 11 8 11, .write 5 11, .binary .add 0 0 10]

def keyOps : List (Op 14 12) :=
  [.publicWord 2 2, .binary .div 3 0 2, .binary .mod 4 0 2,
   .constant 5 1, .binary .sub 6 2 5, .binary .sub 6 6 4,
   .binary .mul 7 3 2, .binary .add 7 7 6, .publicWord 8 7,
   .binary .add 8 8 7, .read 9 8,
   .publicWord 8 8, .binary .add 8 8 3, .read 10 8,
   .binary .div 11 4 4, .binary .mul 10 10 11, .publicWord 12 3,
   .binary .mul 10 10 12, .binary .add 10 10 9, .write 8 10, .binary .add 0 0 5]

def ownerOps : List (Op 14 12) :=
  [.publicWord 2 8, .binary .add 2 2 0, .read 3 2, .publicWord 4 9,
   .binary .add 4 4 3, .read 5 4, .constant 6 1,
   .binary .add 7 5 6, .write 4 7, .publicWord 8 4, .binary .mod 8 5 8,
   .publicWord 9 10, .binary .add 9 9 0, .write 9 8, .binary .add 0 0 6]

theorem row_lengths : digitOps.length = 23 ∧ keyOps.length = 21 ∧ ownerOps.length = 15 :=
  ⟨rfl,rfl,rfl⟩

def procedure (ops : List (Op 14 12)) (v : Parameters w) : Procedure w :=
  ⟨3+ops.length,14,12,OrdinalOpLoop.block w ops 0 1 0,v⟩

def Executes (ops : List (Op 14 12)) (step : Parameters w → Word w → Memory w → Memory w)
    (reg : Fin 14 ↪ Fin r) (pub : Fin 12 → Fin k) (v : Fin k → Word w)
    (state : Word w) (rs : Regs w r) (m : Memory w) : Prop :=
  ∃ es out, trace v state (ops.map (OrdinalOpLoop.relocate reg pub)) rs m =
      some (es,out,step (v ∘ pub) (rs (reg 0)) m) ∧
    out (reg 0)=rs (reg 0)+1 ∧ out (reg 1)=rs (reg 1)

variable (reg : Fin 14 ↪ Fin r) (pub : Fin 12 → Fin k) (v : Fin k → Word w)
    (state : Word w) (rs : Regs w r) (m : Memory w)

set_option maxRecDepth 12000
set_option maxHeartbeats 2500000

theorem digit_trace : Executes digitOps digitStep reg pub v state rs m := by
  simp [Executes,digitOps,digitStep,Function.comp_apply,OrdinalOpLoop.relocate,trace,Op.effect,
    BinaryOp.eval,Function.update,reg.injective.eq_iff]

theorem key_trace : Executes keyOps keyStep reg pub v state rs m := by
  simp [Executes,keyOps,keyStep,Function.comp_apply,OrdinalOpLoop.relocate,trace,Op.effect,
    BinaryOp.eval,Function.update,reg.injective.eq_iff]

theorem owner_trace : Executes ownerOps ownerStep reg pub v state rs m := by
  simp [Executes,ownerOps,ownerStep,Function.comp_apply,OrdinalOpLoop.relocate,trace,Op.effect,
    BinaryOp.eval,Function.update,reg.injective.eq_iff]

end Hierarchy.FactorBucketRAM

end OAI
