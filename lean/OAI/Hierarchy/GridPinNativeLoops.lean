import OAI.Hierarchy.FactorBucketPass

namespace OAI
/-! # Fixed native loops for publishing original factor input pin addresses -/

namespace Hierarchy.GridPinNativeLoops
open ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open FactorBucketRAM
open scoped Fin.CommRing

variable {w r k : ℕ}

private def nz (x : Word w) := BinaryOp.div.eval x x

/-- Initialize a dense array with base-plus-stride addresses. This boots the
tick cursors and, with unit stride, the canonical external rail ordinal map. -/
def seedStep (v : Parameters w) (i : Word w) (m : Memory w) :=
  writeMemory m (v 1+i) (i*v 2+v 3)

def seedOps : List (Op 14 12) :=
  [.publicWord 2 1,.binary .add 2 2 0,.publicWord 3 2,.binary .mul 3 0 3,
   .publicWord 4 3,.binary .add 3 3 4,.write 2 3,.constant 13 1,.binary .add 0 0 13]

/-- One iteration of a class-major scan, with original factors visited in their
initial occurrence order. An unselected row preserves both its output and its
receiving tick's prefix cursor. -/
def factorStep (v : Parameters w) (i : Word w) (m : Memory w) : Memory w :=
  let f := BinaryOp.mod.eval i (v 1)
  let cl := BinaryOp.div.eval i (v 1)
  let hit := 1 - nz (m (v 2+f).val-cl)
  let owner := m (v 3+f).val
  let cp := v 6+owner
  let base := m cp.val
  let len := m (v 4+f*v 5+v 8).val
  let dst := v 7+f
  let old := m dst.val
  writeMemory (writeMemory m dst (old+(base-old)*hit)) cp (base+len*hit)

def factorOps : List (Op 14 12) :=
  [.publicWord 2 1,.binary .mod 3 0 2,.binary .div 4 0 2,
   .publicWord 5 2,.binary .add 5 5 3,.read 5 5,.binary .sub 5 5 4,
   .binary .div 5 5 5,.constant 13 1,.binary .sub 5 13 5,
   .publicWord 6 3,.binary .add 6 6 3,.read 6 6,.publicWord 7 6,.binary .add 7 7 6,
   .read 8 7,.publicWord 9 5,.binary .mul 9 3 9,.publicWord 10 4,.binary .add 9 10 9,
   .publicWord 10 8,.binary .add 9 9 10,.read 9 9,
   .publicWord 10 7,.binary .add 10 10 3,.read 11 10,.binary .sub 12 8 11,
   .binary .mul 12 12 5,.binary .add 12 11 12,.write 10 12,
   .binary .mul 9 9 5,.binary .add 9 8 9,.write 7 9,.binary .add 0 0 13]

/-- Visit the original nonempty buckets in increasing physical order. The
factor's running absolute offset starts at its published factor base. -/
def bucketStep (v : Parameters w) (i : Word w) (m : Memory w) : Memory w :=
  let span := v 1
  let rem := v 2-i*span
  let len := rem+(span-rem)*nz (BinaryOp.div.eval rem span)
  let owner := m (v 3+i).val
  let cp := v 4+owner
  let base := m cp.val
  writeMemory (writeMemory m (v 5+i) base) cp (base+len)

def bucketOps : List (Op 14 12) :=
  [.publicWord 2 1,.publicWord 3 2,.binary .mul 4 0 2,.binary .sub 3 3 4,
   .binary .div 5 3 2,.binary .div 5 5 5,.binary .sub 6 2 3,.binary .mul 6 6 5,
   .binary .add 6 3 6,.publicWord 7 3,.binary .add 7 7 0,.read 7 7,.publicWord 8 4,
   .binary .add 8 8 7,.read 9 8,.publicWord 10 5,.binary .add 10 10 0,.write 10 9,
   .binary .add 9 9 6,.write 8 9,.constant 13 1,.binary .add 0 0 13]

/-- The destination of a bit is a direct bucket lookup plus its original offset. -/
def stone (m : Memory w) (span blocks j : Word w) : Word w :=
  m (blocks+BinaryOp.div.eval j span).val + BinaryOp.mod.eval j span

/-- Publish a literal by reading the captured original tape at a public bit.
Register 2 starts at the length of the exterior field. -/
def literalStep (v : Parameters w) (i : Word w) (m : Memory w) : Memory w :=
  let j := v 2+i
  writeMemory m (v 5+stone m (v 1) (v 3) j) (m (v 4+j).val)

def literalOps : List (Op 14 12) :=
  [.publicWord 2 2,.binary .add 2 2 0,.publicWord 3 1,.binary .div 4 2 3,
   .binary .mod 5 2 3,.publicWord 6 3,.binary .add 6 6 4,.read 6 6,
   .binary .add 6 6 5,.publicWord 7 5,.binary .add 7 7 6,.publicWord 8 4,
   .binary .add 8 8 2,.read 8 8,.write 7 8,.constant 13 1,.binary .add 0 0 13]

/-- Number the endpoint writes by label and side. The original pair ordinal
comes from the rail table, so a change of external labels needs no code change. -/
def endpointStep (v : Parameters w) (i : Word w) (m : Memory w) : Memory w :=
  let e := BinaryOp.div.eval i 2
  let side := BinaryOp.mod.eval i 2
  let j := m (v 2+e).val*2 +side
  writeMemory m (v 4+i) (stone m (v 1) (v 3) j)

def endpointOps : List (Op 14 12) :=
  [.constant 2 2,.binary .div 3 0 2,.binary .mod 4 0 2,.publicWord 5 2,
   .binary .add 5 5 3,.read 5 5,.binary .mul 5 5 2,.binary .add 5 5 4,
   .publicWord 6 1,.binary .div 7 5 6,.binary .mod 8 5 6,.publicWord 9 3,
   .binary .add 9 9 7,.read 9 9,.binary .add 9 9 8,
   .publicWord 10 4,.binary .add 10 10 0,.write 10 9,.constant 13 1,.binary .add 0 0 13]

variable (reg : Fin 14 ↪ Fin r) (pub : Fin 12 → Fin k) (v : Fin k → Word w)
    (state : Word w) (rs : Regs w r) (m : Memory w)

set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

theorem seed_trace : Executes seedOps seedStep reg pub v state rs m := by
  simp [Executes,seedOps,seedStep,Function.comp_apply,OrdinalOpLoop.relocate,trace,Op.effect,
    BinaryOp.eval,Function.update,reg.injective.eq_iff]

theorem factor_trace : Executes factorOps factorStep reg pub v state rs m := by
  simp [Executes,factorOps,factorStep,nz,Function.comp_apply,OrdinalOpLoop.relocate,trace,Op.effect,
    BinaryOp.eval,Function.update,reg.injective.eq_iff]

theorem bucket_trace : Executes bucketOps bucketStep reg pub v state rs m := by
  simp [Executes,bucketOps,bucketStep,nz,Function.comp_apply,OrdinalOpLoop.relocate,trace,Op.effect,
    BinaryOp.eval,Function.update,reg.injective.eq_iff]

theorem literal_trace : Executes literalOps literalStep reg pub v state rs m := by
  simp [Executes,literalOps,literalStep,stone,Function.comp_apply,OrdinalOpLoop.relocate,trace,Op.effect,
    BinaryOp.eval,Function.update,reg.injective.eq_iff]

theorem endpoint_trace : Executes endpointOps endpointStep reg pub v state rs m := by
  simp [Executes,endpointOps,endpointStep,stone,Function.comp_apply,OrdinalOpLoop.relocate,trace,Op.effect,
    BinaryOp.eval,Function.update,reg.injective.eq_iff]

/-- The fixed RAM loop computes precisely its indicated updates in linear time. -/
theorem loop_spec (ops : List (Op 14 12))
    (step : Parameters w → Word w → Memory w → Memory w)
    (exec : ∀ {R K} (reg : Fin 14 ↪ Fin R) (pub : Fin 12 → Fin K) (v : Fin K → Word w)
      (s : Word w) (rs : Regs w R) (mem : Memory w), Executes ops step reg pub v s rs mem)
    (params : Parameters w) (n : ℕ) (fits : n<2^w) (count : params 0=(n:Word w)) :
    (procedure ops params).Spec (fun _ => True)
      (fun mem out => out=iterRows step params mem n) (3+n*(1+ops.length)) := by
  intro pcs regs pubs M pc rg pu exit rom data c mem entry _
  change Fin 12 → Fin pubs at pu
  change Fin 14 ↪ Fin regs at rg
  change ∀ i : Fin 12, M.publicData (pu i)=params i at data
  have eqn : (M.publicData ∘ pu : Fin 12 → Word w)=params := funext data
  have target : M.publicData (pu 0)=(n:Word w) := (data 0).trans count
  obtain ⟨out,run,stop⟩ := advance_rows ops step M pc rg pu exit rom n fits target
    (exec rg pu M.publicData) c entry mem
  exact ⟨_,le_rfl,out,_,run,stop,congrArg (fun v => iterRows step v mem n) eqn⟩

end Hierarchy.GridPinNativeLoops

end OAI
