import OAI.Hierarchy.FactorBucketPass
import OAI.Hierarchy.GridPassageRAMInit
import OAI.Hierarchy.TraceRecordInput

namespace OAI
/-! # Native ROM and memory invariant for the single-tick terminal root directory -/

namespace Hierarchy.GridReceiverTickDirectory
open ThreeFlat RAM PhysicalProcedure Diagonal
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open FactorBucketRAM
open scoped Fin.CommRing

variable {W R K N d T : ℕ}

structure Banks where
  keys : ℕ
  owners : ℕ
  roots : ℕ
  controls : ℕ
  scratch : ℕ

def params (A : Banks) (W N rows : ℕ) : Parameters W :=
  fun i => ((![rows,N,A.keys,A.owners,A.scratch+1,A.roots,A.controls+1,A.controls+4,A.scratch,0,0,0] : Fin 12 → ℕ) i : Word W)

private def equal (a b : Word W) : Word W := 1-BinaryOp.div.eval (a-b) (a-b)

def flag (v : Parameters W) (i : Word W) (m : Memory W) :=
  let f := BinaryOp.mod.eval i (v 1)
  let c := BinaryOp.div.eval i (v 1)
  equal (m (v 2+f).val) c * equal (m (v 3+f).val) (m (v 4).val)

def step (v : Parameters W) (i : Word W) (m : Memory W) :=
  let f := BinaryOp.mod.eval i (v 1)
  let hit := flag v i m
  let count := m (v 6).val
  let dst := v 8+((v 5+count)-v 8)*hit
  writeMemory (writeMemory (writeMemory m dst f) (v 6) (count+hit)) (v 7) (count+hit)

private def keysOps : List (Op 14 12) :=
  [.publicWord 2 1,.binary .mod 3 0 2,.binary .div 4 0 2,
   .publicWord 5 2,.binary .add 5 5 3,.read 5 5,.binary .sub 5 5 4,
   .binary .div 5 5 5,.constant 6 1,.binary .sub 7 6 5]
private def ownerOps : List (Op 14 12) :=
  [.publicWord 5 3,.binary .add 5 5 3,.read 5 5,.publicWord 8 4,.read 8 8,
   .binary .sub 5 5 8,.binary .div 5 5 5,.binary .sub 5 6 5,.binary .mul 7 7 5]
private def putOps : List (Op 14 12) :=
  [.publicWord 8 6,.read 9 8,.publicWord 10 5,.binary .add 10 10 9,.publicWord 11 8,
   .binary .sub 10 10 11,.binary .mul 10 10 7,.binary .add 10 11 10,.write 10 3,
   .binary .add 9 9 7,.write 8 9,.publicWord 8 7,.write 8 9,.binary .add 0 0 6]

def ops := keysOps ++ (ownerOps ++ putOps)
@[simp] theorem ops_length : ops.length=33 := rfl

section Trace
variable (reg : Fin 14 ↪ Fin R) (pub : Fin 12 → Fin K) (v : Fin K → Word W)
  (st : Word W) (rs : Regs W R) (m : Memory W)
local notation "V" => (v ∘ pub)
local notation "rel" => OrdinalOpLoop.relocate reg pub
local notation "fAt" => BinaryOp.mod.eval (rs (reg 0)) (V 1)
local notation "cAt" => BinaryOp.div.eval (rs (reg 0)) (V 1)
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

private theorem keys_trace : ∃ es z, trace v st (keysOps.map rel) rs m=some (es,z,m) ∧
    z (reg 0)=rs (reg 0) ∧ z (reg 1)=rs (reg 1) ∧ z (reg 3)=fAt ∧ z (reg 6)=1 ∧
    z (reg 7)=equal (m (V 2+fAt).val) cAt := by
  simp [keysOps,equal,OrdinalOpLoop.relocate,trace,Op.effect,BinaryOp.eval,Function.update,reg.injective.eq_iff]

private theorem owner_trace (i f k : Word W) (h0 : rs (reg 0)=i) (h3 : rs (reg 3)=f)
    (h6 : rs (reg 6)=1) (h7 : rs (reg 7)=k) :
    ∃ es z, trace v st (ownerOps.map rel) rs m=some (es,z,m) ∧
    z (reg 0)=i ∧ z (reg 1)=rs (reg 1) ∧ z (reg 3)=f ∧ z (reg 6)=1 ∧
    z (reg 7)=k*equal (m (V 3+f).val) (m (V 4).val) := by
  simp [ownerOps,equal,OrdinalOpLoop.relocate,trace,Op.effect,BinaryOp.eval,Function.update,reg.injective.eq_iff,h0,h3,h6,h7]

private theorem put_trace (i : Word W) (h0 : rs (reg 0)=i) (h3 : rs (reg 3)=BinaryOp.mod.eval i (V 1))
    (h6 : rs (reg 6)=1) (h7 : rs (reg 7)=flag V i m) :
    ∃ es z, trace v st (putOps.map rel) rs m=some (es,z,step V i m) ∧
      z (reg 0)=i+1 ∧ z (reg 1)=rs (reg 1) := by
  simp [putOps,step,OrdinalOpLoop.relocate,trace,Op.effect,BinaryOp.eval,Function.update,reg.injective.eq_iff,h0,h3,h6,h7]

theorem executes : Executes ops step reg pub v st rs m := by
  obtain ⟨a,x,ax,x0,x1,x3,x6,x7⟩ := keys_trace reg pub v st rs m
  obtain ⟨b,y,by',y0,y1,y3,y6,y7⟩ := owner_trace reg pub v st x m _ _ _ x0 x3 x6 x7
  obtain ⟨c,z,cz,z0,z1⟩ := put_trace reg pub v st y m _ y0 y3 y6 y7
  refine ⟨a++(b++c),z,?_,z0,z1.trans (y1.trans x1)⟩
  simp [ops,trace_append,ax,by',cz]
end Trace

/-- All predicates used by the compacting scan are comparisons of genuine word values. -/
private theorem equal_eq (a b : Word W) (_hw : 0 < W) : equal a b = if a=b then 1 else 0 := by
  by_cases same : a=b
  · subst a; simp [equal,BinaryOp.eval]
  · have nz : (a-b).val ≠ 0 := fun h => same (sub_eq_zero.mp (Fin.ext h))
    rw [ite_eq_right same,equal]
    simp [BinaryOp.eval,Nat.div_self (Nat.pos_of_ne_zero nz)]

structure Room (A : Banks) (width src n rows : ℕ) : Prop where
  original : src+width ≤ A.roots
  separate : A.roots+rows ≤ A.controls
  key : A.controls+5 ≤ A.keys
  owner : A.keys+n ≤ A.owners
  high : A.owners+n ≤ A.scratch
  address : A.scratch+2 < 2^width
  positive : 0 < width
  nfit : n < 2^width
  length : rows < 2^width

/-- Only the selected prefix and the five countdown words are used by the receiver. -/
structure Published (A : Banks) (ids : List (Fin N)) (input out : Memory W) : Prop where
  roots : ∀ j : Fin ids.length, out (A.roots+j.val)=((ids[j.val]).val:Word W)
  controls : out A.controls=0 ∧ out (A.controls+1)=(ids.length:Word W) ∧
    out (A.controls+2)=0 ∧ out (A.controls+3)=0 ∧ out (A.controls+4)=(ids.length:Word W)
  frame : ∀ a, (a < A.roots ∨ A.roots+ids.length ≤ a) →
    (a < A.controls ∨ A.controls+5 ≤ a) → (a < A.scratch ∨ A.scratch+2 ≤ a) → out a=input a

/-- The packed selected-tick word remains available beside the scan scratch. -/
structure Ticked (A : Banks) (ids : List (Fin N)) (target : Word W) (input out : Memory W) : Prop
    extends Published A ids input out where
  targetAt : out (A.scratch+1)=target

def zeroed (A : Banks) (input : Memory W) := GridPassageRAMInit.clear A.controls 5 input

def build (A : Banks) (W src N rows : ℕ) : Procedure W :=
  ((GridPassageRAMInit.procedure W A.controls 5).seq (TraceAdmission.inputPacker W src (A.scratch+1) 1)).seq
    (FactorBucketRAM.procedure ops (params A W N rows))

/-- Every invocation has fixed hardware size and uses two physical scratch words. -/
theorem hardware (A : Banks) (W src N rows : ℕ) :
    let M := build A W src N rows
    M.labels ≤ 70 ∧ M.registers ≤ 40 ∧ M.slots ≤ 16 := by
  change (build ⟨0,0,0,0,0⟩ 0 0 0 0).labels ≤ 70 ∧ (build ⟨0,0,0,0,0⟩ 0 0 0 0).registers ≤ 40 ∧
    (build ⟨0,0,0,0,0⟩ 0 0 0 0).slots ≤ 16
  decide

def clock (W rows : ℕ) := 4+5*6+(1*(5*W+6)+6)+(3+rows*34)

def put (m : Memory W) (a x : ℕ) : Memory W := fun z => if z=a then (x:Word W) else m z

private theorem write_eq_put (m : Memory W) (a x : ℕ) (fit : a < 2^W) :
    writeMemory m (a:Word W) (x:Word W) = put m a x := by
  funext z
  simp only [writeMemory,put,Fin.val_cast_of_lt fit]

private theorem cast_eq (a b : ℕ) (fa : a < 2^W) (fb : b < 2^W) :
    ((a:Word W)=(b:Word W)) ↔ a=b :=
  ⟨fun h=>by simpa only [Fin.val_cast_of_lt fa,Fin.val_cast_of_lt fb] using congrArg Fin.val h,
    fun h=>congrArg (fun j : ℕ=>(j:Word W)) h⟩

def nextMem (A : Banks) (hit : Prop) [Decidable hit] (f cursor : ℕ) (m : Memory W) :=
  let after := if hit then cursor+1 else cursor
  put (put (put m (if hit then A.roots+cursor else A.scratch) f) (A.controls+1) after) (A.controls+4) after

theorem step_at (A : Banks) (src L i : ℕ) (room : Room A W src N L)
    (hi : i < L) (f : Fin N) (same : i%N=f.val) (cursor : ℕ) (used : cursor ≤ i)
    (key owner target : ℕ) (kf : key < 2^W) (ofit : owner < 2^W) (tf : target < 2^W)
    (m : Memory W) (readK : m (A.keys+f.val)=(key:Word W))
    (readO : m (A.owners+f.val)=(owner:Word W)) (readT : m (A.scratch+1)=(target:Word W))
    (readC : m (A.controls+1)=(cursor:Word W)) :
    step (params A W N L) (i:Word W) m = nextMem A (key=i/N ∧ owner=target) f.val cursor m := by
  obtain ⟨_,destFit,keyFit,ownerFit,high,top,pos,nFit,lFit⟩ := room
  have fN := f.isLt
  have iFit := hi.trans lFit
  have grpFit := (Nat.div_le_self i N).trans_lt iFit
  have modEq : BinaryOp.mod.eval (i:Word W) (N:Word W) = (f.val:Word W) := by
    change Fin.ofNat (2^W) ((i:Word W).val%(N:Word W).val)=_
    rw [Fin.val_cast_of_lt iFit,Fin.val_cast_of_lt nFit,same]; rfl
  have divEq : BinaryOp.div.eval (i:Word W) (N:Word W) = ((i/N:ℕ):Word W) := by
    change Fin.ofNat (2^W) ((i:Word W).val/(N:Word W).val)=_
    rw [Fin.val_cast_of_lt iFit,Fin.val_cast_of_lt nFit]; rfl
  have value : flag (params A W N L) (i:Word W) m =
      if key=i/N ∧ owner=target then 1 else 0 := by
    change equal (m (((A.keys:Word W) + BinaryOp.mod.eval (i:Word W) (N:Word W)).val))
      (BinaryOp.div.eval (i:Word W) (N:Word W)) * equal
      (m (((A.owners:Word W) + BinaryOp.mod.eval (i:Word W) (N:Word W)).val))
      (m (((A.scratch+1:ℕ):Word W).val)) = _
    rw [modEq,divEq,←Nat.cast_add,←Nat.cast_add,Fin.val_cast_of_lt (by omega : A.keys+f.val < 2^W),
      Fin.val_cast_of_lt (by omega : A.owners+f.val < 2^W),Fin.val_cast_of_lt (by omega : A.scratch+1 < 2^W),
      readK,readO,readT,equal_eq _ _ pos,equal_eq _ _ pos]
    by_cases ke : key=i/N <;> by_cases ow : owner=target <;>
      simp [cast_eq _ _ kf grpFit,cast_eq _ _ ofit tf,ke,ow]
  have cnt : m (((A.controls+1:ℕ):Word W).val) = (cursor:Word W) := by
    rw [Fin.val_cast_of_lt (by omega : A.controls+1 < 2^W),readC]
  change writeMemory (writeMemory (writeMemory m
    ((A.scratch:Word W)+(((A.roots:Word W)+m (((A.controls+1:ℕ):Word W).val))-(A.scratch:Word W))*
      flag (params A W N L) (i:Word W) m) (BinaryOp.mod.eval (i:Word W) (N:Word W)))
    ((A.controls+1:ℕ):Word W) (m (((A.controls+1:ℕ):Word W).val)+flag (params A W N L) (i:Word W) m))
    ((A.controls+4:ℕ):Word W) (m (((A.controls+1:ℕ):Word W).val)+flag (params A W N L) (i:Word W) m) = _
  rw [modEq,value,cnt]
  by_cases hit : key=i/N ∧ owner=target
  · simp only [nextMem,ite_eq_left hit,mul_one]
    rw [show (A.scratch:Word W)+((A.roots:Word W)+(cursor:Word W)-(A.scratch:Word W)) =
      ((A.roots+cursor:ℕ):Word W) by push_cast; ring,
      show (cursor:Word W)+1=((cursor+1:ℕ):Word W) by simp]
    rw [write_eq_put _ _ _ (by omega),write_eq_put _ _ _ (by omega),write_eq_put _ _ _ (by omega)]
  · simp only [nextMem,ite_eq_right hit,mul_zero,add_zero]
    rw [write_eq_put _ _ _ (by omega),write_eq_put _ _ _ (by omega),write_eq_put _ _ _ (by omega)]

theorem next_good (A : Banks) (src L i : ℕ) (room : Room A W src N L) (hi : i < L)
    (xs : List (Fin N)) (size : xs.length ≤ i) (m input : Memory W) (ok : Published A xs input m)
    (f : Fin N) (hit : Prop) [Decidable hit] :
    Published A (if hit then xs++[f] else xs) input (nextMem A hit f.val xs.length m) := by
  obtain ⟨_,sep,keys,owners,high,top,_,_,_⟩ := room
  rcases ok with ⟨atRoot,ctrl,frm⟩
  obtain ⟨c0,c1,c2,c3,c4⟩ := ctrl
  by_cases yes : hit
  · simp only [yes,ite_true,nextMem]
    constructor
    · intro j
      have hj := j.isLt
      simp only [List.length_append,List.length_singleton] at hj
      by_cases old : j.val < xs.length
      · simpa [put,List.getElem_append_left old,Nat.ne_of_lt old,show A.roots+j.val ≠ A.controls+4 by omega,
          show A.roots+j.val ≠ A.controls+1 by omega,show A.roots+j.val ≠ A.roots+xs.length by omega] using
          atRoot ⟨j.val,old⟩
      · have last : j.val=xs.length := by omega
        simp [put,last,
          show A.roots+xs.length ≠ A.controls+4 by omega,show A.roots+xs.length ≠ A.controls+1 by omega]
    · simp [put,c0,c2,c3,show A.controls ≠ A.roots+xs.length by omega,
        show A.controls+2 ≠ A.roots+xs.length by omega,show A.controls+3 ≠ A.roots+xs.length by omega]
    · intro a outside ctl scratch
      simp only [List.length_append,List.length_singleton] at outside
      simp [put,show a ≠ A.controls+4 by omega,show a ≠ A.controls+1 by omega,
        show a ≠ A.roots+xs.length by omega,frm a (by omega) ctl scratch]
  · simp only [yes,ite_false,nextMem]
    constructor
    · intro j
      have hj := j.isLt
      simpa [put,show A.roots+j.val ≠ A.controls+4 by omega,
        show A.roots+j.val ≠ A.controls+1 by omega,show A.roots+j.val ≠ A.scratch by omega] using atRoot j
    · simp [put,c0,c2,c3,show A.controls ≠ A.scratch by omega,
        show A.controls+2 ≠ A.scratch by omega,show A.controls+3 ≠ A.scratch by omega]
    · intro a outside ctl scratch
      simp [put,show a ≠ A.controls+4 by omega,show a ≠ A.controls+1 by omega,
        show a ≠ A.scratch by omega,frm a outside ctl scratch]

/-- The unique word packed from the receiving header is its big-endian tick ordinal. -/
theorem unpack_tick (x : Word W) :
    TraceAdmission.inputWord (W:=W) (fun i => x.val.testBit (W-1-i)) 0=x := by
  apply (MotifBinaryPacking.word W).symm.injective
  change (MotifBinaryPacking.word W).symm ((MotifBinaryPacking.word W) _) = _
  rw [Equiv.symm_apply_apply]
  funext i
  change x.val.testBit (W-1-(W*0+(W-1-i.val)))=x.val.testBit i.val
  congr 1
  have := i.isLt
  omega


end Hierarchy.GridReceiverTickDirectory

end OAI
