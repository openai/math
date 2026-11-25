import OAI.ThreeFlat.RAM.HistorySelectedOps
import OAI.ThreeFlat.RAM.HistoryGeneratedStore

namespace OAI
/-! # Leaf, join and array read equations of the actual selected interpreter -/

namespace ThreeFlat.RAM.HistorySelectedOps

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr HistoryCommandParameter HistoryOperandScan
open scoped Fin.CommRing
noncomputable section

variable {W K : ℕ} (initial : Term W K 4) (gates : List (Term W 1 13))
variable (data : Fin (K+1)→Word W) (m : Memory W) (v : Fin 1→Word W)

abbrev control := Fin.last K

def operandPointer := m (m (data (control (K:=K))).val).val

def operands : Fin (K+1)→Word W := fun i => if i=control then operandPointer data m else data i

def tag := (m (m (data (control (K:=K))).val+2).val).val

def entries := core initial ++ (auxiliary W).map (onlyBlock control) ++ gates.map (fun q => geometry q control)

theorem entries_length : (entries initial gates).length=12+gates.length := by
  simp [entries,core,auxiliary]; omega

theorem active (i : Fin (entries initial gates).length) (room : 12+gates.length≤2^W)
    (read : tag data m=i.val) :
    (rows initial gates).eval data m v=((entries initial gates).get i).eval data m v :=
  choice_at (Fin.last K) data m v 0 (entries initial gates) i
    (by simpa only [Nat.zero_add, entries_length] using room)
    (by simpa only [Nat.zero_add, tag, control] using read)

private theorem leafArg_eval (i : Fin (K+1)) :
    (leafArg K control i : Term W (K+1) 0).eval data m Fin.elim0=operands data m i := by
  by_cases h : i=control <;> simp [leafArg,operands,h,operandBlock,operandPointer]

/-- The leaf selector is read from the pointed argument header. Fixed LUTs
and shortened compactors are handled by the same real native scanner. -/
theorem leaf_read (room : 12+gates.length≤2^W) (read : tag data m=0) :
    (rows initial gates).eval data m v=
      HistoryLeafDispatch.readWord (initial.mapPublic Fin.castSucc) (operands data m) m
        (HistoryLeafDispatch.memory (operandPointer data m) m) (v 0) := by
  let i : Fin (entries initial gates).length := ⟨0,by rw [entries_length]; omega⟩
  rw [active initial gates data m v i room read]
  change (replace (leafArg K control) (HistoryLeafDispatch.mountedLeaves initial)).eval _ _ _=_
  rw [eval_replace]
  have args : (fun i => (leafArg K control i : Term W (K+1) 0).eval data m Fin.elim0)=operands data m :=
    funext (leafArg_eval data m)
  rw [args,HistoryLeafDispatch.mountedLeaves,HistoryLeafDispatch.term_eval]
  simp [operands]

theorem origin_read (room : 12+gates.length≤2^W) (read : tag data m=0)
    (input : HistoryLeafDispatch.Input W)
    (record : HistoryLeafDispatch.memory (operandPointer data m) m=input) (zero : input.kind=0) :
    let index := v 0-input.dest
    (rows initial gates).eval data m v=initial.eval (data∘Fin.castSucc) m
      ![BinaryOp.eval .div index 4,BinaryOp.eval .mod index 4,input.a,input.b] := by
  dsimp only
  rw [leaf_read initial gates data m v room read,record]
  simp only [HistoryLeafDispatch.readWord,zero,ite_true,Term.eval_mapPublic]
  congr 1
  funext i
  simp [operands,control]

theorem join_read (room : 12+gates.length≤2^W) (read : tag data m=1) :
    (rows initial gates).eval data m v=HistoryJoinScan.readWord
      (HistoryJoinScan.fetch (operandPointer data m) m) m (v 0) := by
  let i : Fin (entries initial gates).length := ⟨1,by rw [entries_length]; omega⟩
  rw [active initial gates data m v i room read]
  change (replace (fun _ : Fin 1 => (Term.parameter control).load)
    (HistoryJoinScan.term (w:=W) (0:Fin 1))).eval _ _ _=_
  rw [eval_replace,HistoryJoinScan.eval_term]
  rfl

/-- Full semantic read at the native copy opcode in both the 14-word
bounded pair and 21-word table/compactor batch. Its prerequisites are the
already-produced child/source rows, pin map and actual six fields. -/
theorem copy_record {F : Type*} {n h p : ℕ} {arity : Fin n→ℕ}
    (N : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
    (id : ((Fin 3→Bool)→F)→ℕ) (q : HistoryJoinScan.Header ℕ)
    (i : Fin n) (row : Fin (N i).cells) (j : Fin 4) (pins : ℕ→ℕ)
    (room : 12+gates.length≤2^W) (op : tag data m=1)
    (header : HistoryJoinScan.fetch (operandPointer data m) m=q.words)
    (key : v 0=((q.dest+(4*row.val+j.val):ℕ):Word W))
    (mapWords : ∀ z,pins z.val=BitLayout.sourceAddress (BitNetwork.Ordered.resolve N wire i (.pin z)))
    (shape : q.oldPins=arity i ∧ q.newPins=p ∧ q.offset=h+∑ z : Fin i.val,(N (Fin.castLE i.isLt.le z)).internal)
    (srcRange : q.source+4*(N i).cells≤2^W) (pinRange : q.pins+q.oldPins≤2^W)
    (oldRange : 2+q.oldPins<2^W) (small : HistoryCompiledRows.metadata id (N i) row j<2^W)
    (child : HistoryCompiledRows.Records id (N i) q.source m)
    (addresses : ∀ t,t<q.oldPins→m (q.pins+t)=(pins t:Word W)) :
    (rows initial gates).eval data m v=
      (HistoryCompiledRows.metadata id (BitNetwork.Ordered.glue N wire) (finSigmaFinEquiv ⟨i,row⟩) j:Word W) := by
  rw [join_read initial gates data m v room op,header,key]
  have hr := HistoryCompiledRows.segment_record N wire id q m i row j pins mapWords shape
    (by omega) srcRange pinRange oldRange small child addresses
  have valid : q.dest≤q.dest+(4*row.val+j.val) ∧ q.dest+(4*row.val+j.val)<q.dest+4*(N i).cells := by
    have := row.isLt;have := j.isLt;omega
  have addr (a : ℕ) : Fin.ofNat (2^W) a = (a : Word W) := by
    apply Fin.ext
    simp only [Fin.val_ofNat, Fin.val_natCast]
  simpa only [fillSegment,ite_eq_left valid,addr] using hr

/-- The bounded chronological join of the kernel and old sites uses a
two-run affine pin map. The comparison and both additions operate on the
actual operands in its five-word scratch header. -/
theorem port_read (room : 12+gates.length≤2^W) (read : tag data m=8) :
    let arg := operandPointer data m
    let x := BinaryOp.eval .div (v 0-m arg.val) 1
    let k := m (arg+2).val
    (rows initial gates).eval data m v=
      if x<k then m (arg+3).val+x else m (arg+4).val+(x-k) := by
  let i : Fin (entries initial gates).length := ⟨8,by rw [entries_length]; omega⟩
  rw [active initial gates data m v i room read]
  change (onlyBlock control (program (HistoryPortMap.word W 1) (0:Fin 1) 1
    ![Operand.row,Operand.header 2,Operand.header 3,Operand.header 4])).eval _ _ _=_
  rw [onlyBlock_eval,HistoryOperandScan.eval,HistoryPortMap.eval_word]
  rfl

/-- Actual interleaved old/new pointer lookup through the current S5 row
and S2 pair bases. This is the second command of each physical cursor leaf. -/
theorem pair_read (room : 12+gates.length≤2^W) (read : tag data m=9) :
    let arg := operandPointer data m
    (rows initial gates).eval data m v = (HistoryPairSeeds.program W 0).eval (fun _ => arg) m
      ![BinaryOp.eval .div (v 0-m arg.val) 1,m (arg+2).val,m (arg+3).val] := by
  dsimp only
  let i : Fin (entries initial gates).length := ⟨9,by rw [entries_length]; omega⟩
  rw [active initial gates data m v i room read]
  change (onlyBlock control (program (HistoryPairSeeds.program W 0) (0:Fin 1) 1
    ![Operand.row,Operand.header 2,Operand.header 3])).eval _ _ _=_
  rw [onlyBlock_eval,HistoryOperandScan.eval]
  apply congrArg _
  funext j
  fin_cases j <;> rfl

/-- The native array source is the two-level operand block, and the relative
cursor comes from this operation's own destination base. -/
theorem array_read (copy : Bool) (room : 12+gates.length≤2^W)
    (read : tag data m=if copy then 10 else 11) :
    let arg := operandPointer data m
    let offset := BinaryOp.eval .div (v 0-m arg.val) 1
    let src := m (arg+2).val+offset
    (rows initial gates).eval data m v=if copy then m src.val else src := by
  dsimp only
  cases copy
  · let i : Fin (entries initial gates).length := ⟨11,by rw [entries_length]; omega⟩
    rw [active initial gates data m v i room read]
    change (onlyBlock control (Term.binary .add (operand (0:Fin 1) 1 (.header 2))
      (operand (0:Fin 1) 1 .row))).eval _ _ _=_
    rw [onlyBlock_eval]
    simp [operand,field,operandPointer,Term.eval,BinaryOp.eval]
  · let i : Fin (entries initial gates).length := ⟨10,by rw [entries_length]; omega⟩
    rw [active initial gates data m v i room read]
    change (onlyBlock control ((Term.binary .add (operand (0:Fin 1) 1 (.header 2))
      (operand (0:Fin 1) 1 .row)).load)).eval _ _ _=_
    rw [onlyBlock_eval]
    simp [operand,field,operandPointer,Term.eval,BinaryOp.eval]

/-- All pin-map cases used by the physical bounded joins. The live opcode,
start and three scalar operands are the literal words of the generated
argument row. A gather reads its already-computed physical address cache. -/
theorem map_word (op target split first second x : ℕ) (room : 12+gates.length≤2^W)
    (tagOK : tag data m=op) (mode : op=8 ∨ op=10 ∨ op=11)
    (start : m (operandPointer data m).val=(target:Word W))
    (field : m (operandPointer data m+2).val=(split:Word W))
    (firstVal : op=8→m (operandPointer data m+3).val=(first:Word W))
    (secondVal : op=8→m (operandPointer data m+4).val=(second:Word W))
    (key : v 0=((target+x:ℕ):Word W)) (fit : x<2^W) (bound : split<2^W)
    (source : op=10→split+x<2^W) :
    (rows initial gates).eval data m v=
      if op=8 then (HistoryPortMap.piecewise x split first second:Word W)
      else if op=10 then m (split+x) else ((split+x:ℕ):Word W) := by
  have delta : BinaryOp.eval .div (v 0-m (operandPointer data m).val) 1=(x:Word W) := by
    rw [start,key,Nat.cast_add,add_sub_cancel_left]
    simp [BinaryOp.eval,Fin.val_cast_of_lt fit,Nat.mod_eq_of_lt (show 1<2^W by omega)]
  rcases mode with h|h|h
  · rw [port_read initial gates data m v room (tagOK.trans h),delta,field,firstVal h,secondVal h]
    rw [ite_eq_left h]
    by_cases c : x<split
    · have hw : (x:Word W)<(split:Word W) := by
        change (x:Word W).val<_ ; rw [Fin.val_cast_of_lt fit,Fin.val_cast_of_lt bound];exact c
      simp [hw,HistoryPortMap.piecewise,c]
    · have hw : ¬(x:Word W)<(split:Word W) := by
        change ¬(x:Word W).val<_ ; rw [Fin.val_cast_of_lt fit,Fin.val_cast_of_lt bound];exact c
      simp [hw,HistoryPortMap.piecewise,c,Nat.cast_sub (Nat.le_of_not_lt c)]
  · rw [array_read initial gates data m v true room (tagOK.trans h),delta,field]
    simp [h,←Nat.cast_add,Fin.val_cast_of_lt (source h)]
  · rw [array_read initial gates data m v false room (tagOK.trans h),delta,field]
    simp [h,Nat.cast_add]


end
end ThreeFlat.RAM.HistorySelectedOps

end OAI
