import OAI.Optimization.LinearProgramming.RAM.Loops
import OAI.Optimization.LinearProgramming.RAM.RAMCount

/-! Constant-instruction streaming copy with direct scalar scratch register zero.
Copying forward permits source address zero; copying backward permits destination
address zero. The direction is fixed at program assembly time. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open RAM RAM.Block RAM.Tape

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem safe_data_write (s : Memory K) (hs : Good P s) (i : Nat) (q : K) (hq : P q) :
    Good P (s.putData i q) := by
  intro k; by_cases hk : k = i
  · simpa [hk] using hq
  · simpa [Memory.putData_ne s hk] using hs k

private def advance (rev : Bool) (a : Nat) := if rev then a - 1 else a + 1
private def advanceOp (rev : Bool) (r : Nat) : Instr := if rev then .decr r r else .incr r r

private theorem advance_run (rev : Bool) (s : Memory K) (hs : Good P s) (r : Nat) :
    Eval (Good P) (.op (advanceOp rev r)) s 1 (s.putIndex r (advance rev (s.index r))) := by
  cases rev
  · exact eval_incr s hs r r
  · exact eval_decr s hs r r

private def copyStep (rev : Bool) : Block := .straight
  [.load 0 0, .store 1 0, advanceOp rev 0, advanceOp rev 1, .decr 2 2]

/-- Registers 0 and 1 are the current source and destination addresses, register
2 counts remaining words, and address register 3 contains zero. -/
def copyWindow (rev : Bool) : Block := .loop (.addrLT 3 2) (copyStep rev)

/-- Initial pointer for the selected direction, supplied by the caller. -/
def startPointer (rev : Bool) (base count : Nat) : Nat := if rev then base+count-1 else base

private def pointer (rev : Bool) (base n j : Nat) : Nat :=
  if rev then base+n-1-j else base+j

private def offset (rev : Bool) (n j : Nat) : Nat := if rev then n-1-j else j

private theorem pointer_at (rev : Bool) (base n j : Nat) (hj : j < n) :
    pointer rev base n j = base+offset rev n j := by cases rev <;> simp [pointer, offset]; omega

private theorem pointer_next (rev : Bool) (base n j : Nat) :
    advance rev (pointer rev base n j) = pointer rev base n (j+1) := by
  cases rev <;> simp [advance,pointer] <;> omega

private theorem offset_lt (rev : Bool) {n j} (hj : j < n) : offset rev n j < n := by
  cases rev <;> simp [offset] <;> omega

private theorem offset_ne (rev : Bool) {n j k : Nat} (hj : j < n) (hk : k < n) (h : j ≠ k) :
    offset rev n j ≠ offset rev n k := by cases rev <;> simp [offset] <;> omega

private theorem copy_step_run (rev : Bool) (s : Memory K) (hs : Good P s) :
    ∃ t, Eval (Good P) (copyStep rev) s 5 t ∧
      (∀ k, t.data k = if k = s.index 1 ∨ k = 0 then s.data (s.index 0) else s.data k) ∧
      t.index 0 = advance rev (s.index 0) ∧ t.index 1 = advance rev (s.index 1) ∧
      t.index 2 = s.index 2-1 ∧ (∀ k, 3 ≤ k → t.index k = s.index k) := by
  let val := s.data (s.index 0)
  let s1 := s.putData 0 val
  let s2 := s1.putData (s.index 1) val
  let s3 := s2.putIndex 0 (advance rev (s.index 0))
  let s4 := s3.putIndex 1 (advance rev (s.index 1))
  let t := s4.putIndex 2 (s.index 2-1)
  have h1 : Good P s1 := safe_data_write s hs _ _ (hs _)
  have h2 : Good P s2 := safe_data_write s1 h1 _ _ (hs _)
  have a : Eval (Good P) (.op (.load 0 0)) s 1 s1 := Eval.op_load s _ _ hs h1
  have b : Eval (Good P) (.op (.store 1 0)) s1 1 s2 := by
    simpa only [s2, s1, Memory.putData_same, Memory.putData_index] using
      (Eval.op_store s1 1 0 h1 (safe_data_write s1 h1 _ _ (h1 _)))
  have c : Eval (Good P) (.op (advanceOp rev 0)) s2 1 s3 := advance_run rev s2 h2 0
  have d : Eval (Good P) (.op (advanceOp rev 1)) s3 1 s4 := by
    simpa only [s3, Memory.putIndex_ne _ (by decide : 1 ≠ 0), s2, s1, Memory.putData_index]
      using advance_run rev s3 c.safe_end 1
  have e : Eval (Good P) (.op (.decr 2 2)) s4 1 t := by
    simpa only [s4, s3, Memory.putIndex_ne _ (by decide : 2 ≠ 1), Memory.putIndex_ne _ (by decide : 2 ≠ 0),
      s2, s1, Memory.putData_index] using eval_decr s4 d.safe_end 2 2
  refine ⟨t,a.seq (b.seq (c.seq (d.seq (e.seq (.skip e.safe_end))))), ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    change (s1.putData (s.index 1) val).data k = _
    by_cases hk : k = s.index 1
    · subst k; simp [val]
    · rw [Memory.putData_ne _ hk]
      by_cases h0 : k = 0
      · subst k; simp [s1,val]
      · simp [s1,val,hk,h0,Memory.putData_ne]
  · simp [t,s4,s3]
  · simp [t,s4]
  · simp [t]
  · intro k hk; simp [t,s4,s3,s2,s1,Memory.putIndex_ne _ (by omega : k ≠ 2),
      Memory.putIndex_ne _ (by omega : k ≠ 1), Memory.putIndex_ne _ (by omega : k ≠ 0)]

private structure CopyInv (rev : Bool) (n src dst : Nat) (initial : Memory K)
    (j : Nat) (s : Memory K) (P : K → Prop) : Prop where
  safe : Good P s
  readPtr : s.index 0 = pointer rev src n j
  writePtr : s.index 1 = pointer rev dst n j
  remaining : s.index 2 = n-j
  zero : s.index 3 = 0
  indices : ∀ k, 4 ≤ k → s.index k = initial.index k
  done : ∀ k < j, s.data (dst+offset rev n k) = initial.data (src+offset rev n k)
  pending : ∀ k, j ≤ k → k < n → s.data (src+offset rev n k) = initial.data (src+offset rev n k)
  untouched : ∀ a, a ≠ 0 → (a < dst ∨ dst+n ≤ a) → s.data a = initial.data a

/-- A bounded streaming copy of disjoint windows. In particular this supports copying
the original input out of address zero and copying a staged output back to address zero. -/
theorem copyWindow_correct (rev : Bool) (n src dst : Nat) (s : Memory K) (hs : Good P s)
    (hsrc : s.index 0 = startPointer rev src n) (hdst : s.index 1 = startPointer rev dst n)
    (hsize : s.index 2 = n) (hz : s.index 3 = 0) (hsep : src+n ≤ dst ∨ dst+n ≤ src)
    (hmode : if rev then 0 < src else 0 < dst) :
    ∃ t, Eval (Good P) (copyWindow rev) s (n*(5+2)+1) t ∧
      (∀ k < n, t.data (dst+k) = s.data (src+k)) ∧
      (∀ a, a ≠ 0 → (a < dst ∨ dst+n ≤ a) → t.data a = s.data a) ∧
      (∀ k, 4 ≤ k → t.index k = s.index k) := by
  let I := fun j t => CopyInv rev n src dst s j t P
  have hstart : I 0 s :=
    ⟨hs,by simpa [startPointer,pointer] using hsrc,by simpa [startPointer,pointer] using hdst,
      by simpa using hsize,hz,fun _ _ => rfl,fun k hk => (Nat.not_lt_zero _ hk).elim,
      fun _ _ _ => rfl,fun _ _ _ => rfl⟩
  have body (j : Nat) (hj : j < n) (w : Memory K) (hw : I j w) :
      (Cond.addrLT 3 2).test w = true ∧ ∃ t, Eval (Good P) (copyStep rev) w 5 t ∧ I (j+1) t := by
    refine ⟨by simp [Cond.test,hw.zero,hw.remaining, Nat.sub_pos_of_lt hj], ?_⟩
    obtain ⟨t,hr,hd,ha,hb,hn,hf⟩ := copy_step_run rev w hw.safe
    have rd := (hw.readPtr.trans (pointer_at rev src n j hj))
    have wd := (hw.writePtr.trans (pointer_at rev dst n j hj))
    have val := hw.pending j le_rfl hj
    have curr := offset_lt rev hj
    refine ⟨t,hr,hr.safe_end,by rw [ha,hw.readPtr,pointer_next],by rw [hb,hw.writePtr,pointer_next],
      by rw [hn,hw.remaining]; omega,(hf 3 le_rfl).trans hw.zero,
      fun k hk => (hf k (by omega)).trans (hw.indices k hk),?_,?_,?_⟩
    · intro k hk
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hkj | rfl
      · have off := offset_ne rev (lt_trans hkj hj) hj hkj.ne
        have hneq : dst+offset rev n k ≠ 0 := by cases rev <;> simp [offset] at * <;> omega
        rw [hd,wd,ite_eq_right (by omega)]
        exact hw.done k hkj
      · rw [hd,wd,ite_eq_left (Or.inl rfl),rd,val]
    · intro k hk hkn
      have hkn' := offset_lt rev hkn
      have hzero : src+offset rev n k ≠ 0 := by cases rev <;> simp [offset] at * <;> omega
      rw [hd,wd,ite_eq_right (by rcases hsep with hsep | hsep <;> omega)]
      exact hw.pending k (by omega) hkn
    · intro a h0 hwindow
      rw [hd,wd,ite_eq_right (by rcases hwindow with h|h <;> omega)]
      exact hw.untouched a h0 hwindow
  obtain ⟨t,hr,ht⟩ := Eval.loop_invariant_exact I s n 5 hstart body
    (fun w hw => ⟨by simp [Cond.test,hw.zero,hw.remaining],hw.safe⟩)
  refine ⟨t,hr,?_,ht.untouched,ht.indices⟩
  intro k hk
  cases rev with
  | false => exact ht.done k hk
  | true =>
    have h := ht.done (n-1-k) (by omega)
    simpa only [offset, ↓reduceIte, show n-1-(n-1-k)=k by omega] using h

end PrimalDual
end LinearProgramming
end Optimization
end OAI
