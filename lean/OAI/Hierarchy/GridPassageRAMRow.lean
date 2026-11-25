import OAI.ThreeFlat.RAM.OrdinalOpLoop

namespace OAI
/-! # Native fixed-length row of the first-passage compiler -/

namespace Hierarchy.GridPassageRAMRow

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
variable {w r k : ℕ}

abbrev Parameters (w : ℕ) := Fin 12 → Word w

/-- Limit, radix, axis count, capacity, direction, cell, powers, touch, count,
chosen, mark, and inactive scratch. -/
def values (w limit g k B dir cell powers touch counts chosen mark scratch : ℕ) : Parameters w :=
  ![limit,g,k,B,dir,cell,powers,touch,counts,chosen,mark,scratch]

structure Visit (w : ℕ) where
  rail : Word w
  position : Word w
  key : Word w

/-- Replace the direction digit of the stored cell by the current longitudinal index. -/
def visit (v : Parameters w) (i : Word w) (m : Memory w) : Visit w :=
  let e := BinaryOp.div.eval i (v 1)
  let t := BinaryOp.mod.eval i (v 1)
  let d := m (v 4+e).val
  let rep := m (v 5+e).val
  let stride := m (v 6+d).val
  let digit := BinaryOp.mod.eval (BinaryOp.div.eval rep stride) (v 1)
  ⟨e,t,(rep-digit*stride+t*stride)*v 2+d⟩

def nonzeroBit (a : Word w) : Word w := BinaryOp.div.eval a a

/-- Unsigned less-than as a native quotient followed by a nonzero test. -/
def unsignedLt (a b : Word w) : Word w := nonzeroBit (BinaryOp.div.eval b (a+1))

/-- The integer quotient is positive exactly when another chosen slot is available. -/
def active (B old tag position : Word w) : Word w :=
  unsignedLt old B * nonzeroBit (tag-position)

/-- The first write uses the scratch address on an inactive row and rewrites
its existing value. The counter and mark then receive their new values. -/
def commit (v : Parameters w) (i : Word w) (z : Visit w) (addr old flag : Word w)
    (m : Memory w) : Memory w :=
  let target := v 9+(z.key*v 3+old)
  let dst := v 11+(target-v 11)*flag
  let before := m dst.val
  let saved := writeMemory m dst (before+(z.rail-before)*flag)
  writeMemory (writeMemory saved addr (old+flag)) (v 10+i) flag

def wordStep (v : Parameters w) (i : Word w) (m : Memory w) : Memory w :=
  let z := visit v i m
  let addr := v 8+z.key
  let old := m addr.val
  let tag := m (v 7+z.rail).val
  commit v i z addr old (active (v 3) old tag z.position) m

/-- Registers 0 and 1 are the driver cursor and bound. -/
private def keyOps : List (Op 18 12) :=
  [.publicWord 2 1,.binary .div 3 0 2,.binary .mod 4 0 2,
   .publicWord 5 4,.binary .add 5 5 3,.read 6 5,
   .publicWord 5 5,.binary .add 5 5 3,.read 7 5,
   .publicWord 5 6,.binary .add 5 5 6,.read 8 5,
   .binary .div 9 7 8,.binary .mod 9 9 2,.binary .mul 9 9 8,
   .binary .sub 7 7 9,.binary .mul 9 4 8,.binary .add 7 7 9,
   .publicWord 9 2,.binary .mul 10 7 9,.binary .add 10 10 6]

private def eligibilityOps : List (Op 18 12) :=
  [.publicWord 5 8,.binary .add 11 5 10,.read 12 11,.publicWord 13 3,.constant 15 1,
   .binary .add 9 12 15,.binary .div 9 13 9,.binary .div 14 9 9,
   .publicWord 5 7,.binary .add 5 5 3,.read 5 5,.binary .sub 5 5 4,
   .binary .div 5 5 5,.binary .mul 14 14 5]

private def putOps : List (Op 18 12) :=
  [.publicWord 16 9,.binary .mul 9 10 13,.binary .add 9 9 12,.binary .add 16 16 9,
   .publicWord 5 11,.binary .sub 9 16 5,.binary .mul 9 9 14,.binary .add 16 5 9,
   .read 5 16,.binary .sub 9 3 5,.binary .mul 9 9 14,.binary .add 5 5 9,.write 16 5,
   .binary .add 5 12 14,.write 11 5,.publicWord 17 10,.binary .add 17 17 0,.write 17 14,
   .binary .add 0 0 15]

def ops : List (Op 18 12) := keyOps ++ (eligibilityOps ++ putOps)

@[simp] theorem ops_length : ops.length = 54 := rfl

def procedure (v : Parameters w) : Procedure w :=
  ⟨3+ops.length,18,12,OrdinalOpLoop.block w ops 0 1 0,v⟩

variable (reg : Fin 18 ↪ Fin r) (pub : Fin 12 → Fin k) (v : Fin k → Word w)
    (state : Word w) (rs : Regs w r) (m : Memory w)
local notation "V" => (v ∘ pub)
local notation "mount" => OrdinalOpLoop.relocate reg pub
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

private theorem key_trace :
    let z := visit V (rs (reg 0)) m
    ∃ es out, trace v state (keyOps.map mount) rs m = some (es,out,m) ∧
      out (reg 0) = rs (reg 0) ∧ out (reg 1) = rs (reg 1) ∧
      out (reg 3) = z.rail ∧ out (reg 4) = z.position ∧ out (reg 10) = z.key := by
  simp [keyOps, visit, Function.comp_apply, OrdinalOpLoop.relocate, trace, Op.effect,
    BinaryOp.eval, Function.update, reg.injective.eq_iff]

private theorem eligibility_trace (z : Visit w) (e : rs (reg 3)=z.rail)
    (t : rs (reg 4)=z.position) (key : rs (reg 10)=z.key) :
    let addr := V 8+z.key
    let old := m addr.val
    let f := active (V 3) old (m (V 7+z.rail).val) z.position
    ∃ es out, trace v state (eligibilityOps.map mount) rs m = some (es,out,m) ∧
      out (reg 0)=rs (reg 0) ∧ out (reg 1)=rs (reg 1) ∧ out (reg 3)=z.rail ∧
      out (reg 10)=z.key ∧ out (reg 11)=addr ∧ out (reg 12)=old ∧ out (reg 13)=V 3 ∧
      out (reg 14)=f ∧ out (reg 15)=1 := by
  simp [eligibilityOps, active, unsignedLt, nonzeroBit, Function.comp_apply, OrdinalOpLoop.relocate, trace,
    Op.effect, BinaryOp.eval, Function.update, reg.injective.eq_iff,e,t,key]

private theorem put_trace (i : Word w) (z : Visit w) (addr old flag : Word w)
    (cur : rs (reg 0)=i) (e : rs (reg 3)=z.rail) (key : rs (reg 10)=z.key)
    (a : rs (reg 11)=addr) (count : rs (reg 12)=old) (B : rs (reg 13)=V 3)
    (flagAt : rs (reg 14)=flag) (one : rs (reg 15)=1) :
    ∃ es out, trace v state (putOps.map mount) rs m = some (es,out,commit V i z addr old flag m) ∧
      out (reg 0)=i+1 ∧ out (reg 1)=rs (reg 1) := by
  simp [putOps, commit, Function.comp_apply, OrdinalOpLoop.relocate, trace, Op.effect,
    BinaryOp.eval, Function.update, reg.injective.eq_iff, cur,e,key,a,count,B,flagAt,one]

/-- The cursor in the relocated block advances once, the loop bound is
preserved, and the three external writes implement the specified transition. -/
theorem row_trace :
    ∃ es out, trace v state (ops.map mount) rs m =
      some (es,out,wordStep V (rs (reg 0)) m) ∧
      out (reg 0)=rs (reg 0)+1 ∧ out (reg 1)=rs (reg 1) := by
  let i := rs (reg 0)
  let z := visit V i m
  let addr := V 8+z.key
  let old := m addr.val
  let f := active (V 3) old (m (V 7+z.rail).val) z.position
  obtain ⟨ae,ar,at₁,a0,a1,a3,a4,a10⟩ := key_trace reg pub v state rs m
  obtain ⟨be,br,at₂,b0,b1,b3,b10,b11,b12,b13,b14,b15⟩ :=
    eligibility_trace reg pub v state ar m z a3 a4 a10
  obtain ⟨ce,cr,at₃,c0,c1⟩ := put_trace reg pub v state br m i z addr old f
    (b0.trans a0) b3 b10 b11 b12 b13 b14 b15
  refine ⟨ae++(be++ce),cr,?_,c0,c1.trans (b1.trans a1)⟩
  simp [ops, trace_append, at₁,at₂,at₃,wordStep,i,z,addr,old,f]

end Hierarchy.GridPassageRAMRow

end OAI
