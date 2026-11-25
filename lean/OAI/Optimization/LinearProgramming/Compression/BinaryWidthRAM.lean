import OAI.Optimization.LinearProgramming.Compression.BinaryPublicWidth

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM OracleSpec.MinorLog

private def selectWidth (out : ℕ) : Block :=
  .branch (.scalarLT 3 5) .skip (.op (.copy out 4))

private theorem selectWidth_spec (m : Memory ℚ) (a j out : ℕ) {P : ℚ → Prop}
    (safe : m.AllData P) (bit : m.data 3 = ((integerDigit a j : ℕ) : ℚ)) (one : m.data 5 = 1)
    (pos : m.data 4 = ((j+1 : ℕ) : ℚ)) (old : m.data out = (width (a % 2^j) : ℚ)) :
    ∃ t, Block.Eval (Memory.AllData P) (selectWidth out) m 2 t ∧
      t.data out = (width (a % 2^(j+1)) : ℚ) ∧ t.index = m.index ∧
      ∀ i, i ≠ out → t.data i = m.data i := by
  rcases integerDigit_cases a j with h | h
  · refine ⟨m,Block.Eval.branchTrue (by simp [Cond.test,bit,one,h]) (.skip safe),?_,rfl,fun _ _ => rfl⟩
    simpa only [width_mod_pow_succ,h,ite_true] using old
  · let t := m.putData out (m.data 4)
    have w := Block.Eval.op_copy m out 4 safe (safe.putData _ (safe 4))
    refine ⟨t,Block.Eval.branchFalse (by simp [Cond.test,bit,one,h]) w,?_,rfl,?_⟩
    · simp [t,pos,width_mod_pow_succ,h]
    · intro i hi; simp [t,hi]

private def widthScanBody (out : ℕ) : Block := .seq (.op (.load 3 1)) <|
  .seq (selectWidth out) (.seq (.op (.add 4 4 5)) (.op (.incr 1 1)))

/-- Compute a word's exact canonical width, preserving the padded little-endian tape. -/
def widthScanBlock (out : ℕ) : Block := .seq (.op (.const 5 1)) <|
  .seq (.op (.const 4 1)) (.seq (.op (.const out 1)) (.forRange 2 0 (widthScanBody out)))

theorem widthScanBlock_spec (m : Memory ℚ) (a k base out : ℕ) {P : ℚ → Prop}
    (hm : m.AllData P) (ho : out = 1 ∨ out = 2) (hk : m.index 0=k) (hb : m.index 1=base)
    (hbase : 10 ≤ base) (ha : a < 2^k)
    (digits : ∀ j<k, m.data (base+j)=((integerDigit a j : ℕ) : ℚ))
    (hP : ∀ z : ℕ, z ≤ k+1 → P (z : ℚ)) :
    ∃ t, Block.Eval (Memory.AllData P) (widthScanBlock out) m (8*k+5) t ∧
      t.data out = (width a : ℚ) ∧ t.data 4 = ((k+1 : ℕ) : ℚ) ∧ t.data 5 = 1 ∧
      t.index 1 = base+k ∧ (∀ i, i≠out → i≠3 → i≠4 → i≠5 → t.data i=m.data i) ∧
      (∀ i, i≠1 → i≠2 → t.index i=m.index i) := by
  let I := fun (j : ℕ) (s : Memory ℚ) => s.AllData P ∧ s.index 2=j ∧ s.index 0=k ∧
    s.index 1=base+j ∧ s.data out=(width (a % 2^j):ℚ) ∧ s.data 4=((j+1 : ℕ):ℚ) ∧ s.data 5=1 ∧
    (∀ i, i≠out → i≠3 → i≠4 → i≠5 → s.data i=m.data i) ∧
    (∀ i, i≠1 → i≠2 → s.index i=m.index i)
  have h1 : P 1 := by simpa using hP 1 (by omega)
  have o3 : out ≠ 3 := by omega
  have o4 : out ≠ 4 := by omega
  have o5 : out ≠ 5 := by omega
  let m1 := m.putData 5 1
  let m2 := m1.putData 4 1
  let z := m2.putData out 1
  have e1 := Block.Eval.op_const m 5 1 hm (hm.putData 5 h1)
  have e2 := Block.Eval.op_const m1 4 1 e1.safe_end (e1.safe_end.putData 4 h1)
  have e3 := Block.Eval.op_const m2 out 1 e2.safe_end (e2.safe_end.putData out h1)
  have init : I 0 (z.putIndex 2 0) := by
    refine ⟨e3.safe_end,by simp,?_,?_,?_,?_,?_,?_,?_⟩
    · simp [z,m2,m1,hk]
    · simp [z,m2,m1,hb]
    · simp [z,width,Nat.mod_one]
    · simp [z,m2,Ne.symm o4]
    · simp [z,m2,m1,Ne.symm o5]
    · intro i io _ i4 i5; simp [z,m2,m1,io,i4,i5]
    · intro i _ i2; simp [z,m2,m1,i2]
  have body (j : ℕ) (hj : j<k) (s : Memory ℚ) (hs : I j s) :
      ∃ t, Block.Eval (Memory.AllData P) (widthScanBody out) s 5 t ∧ I (j+1) (t.putIndex 2 (t.index 2+1)) := by
    obtain ⟨safe,cnt,size,cur,widthj,pos,one,frame,idx⟩ := hs
    let s1 := s.putData 3 (s.data (s.index 1))
    have load := Block.Eval.op_load s 3 1 safe (safe.putData 3 (safe _))
    have bit : s1.data 3 = ((integerDigit a j : ℕ):ℚ) := by
      rw [show s1.data 3 = s.data (s.index 1) from Memory.putData_same ..,cur]
      exact (frame (base+j) (by omega) (by omega) (by omega) (by omega)).trans (digits j hj)
    obtain ⟨w,sel,width',wi,wkeep⟩ := selectWidth_spec s1 a j out load.safe_end bit
      (by simpa [s1] using one) (by simpa [s1] using pos) (by simpa [s1,o3] using widthj)
    have wpos : w.data 4 = ((j+1 : ℕ):ℚ) := (wkeep 4 (Ne.symm o4)).trans (by simpa [s1] using pos)
    have wone : w.data 5 = 1 := (wkeep 5 (Ne.symm o5)).trans (by simpa [s1] using one)
    have addPos : w.data 4 + w.data 5 = ((j+1+1 : ℕ):ℚ) := by simp [wpos,wone]
    let w1 := w.putData 4 (w.data 4 + w.data 5)
    let t := w1.putIndex 1 (w1.index 1+1)
    have add := Block.Eval.op_add w 4 4 5 sel.safe_end (sel.safe_end.putData _ (addPos ▸ hP _ (by omega)))
    have inc := Block.Eval.op_incr w1 1 1 add.safe_end (add.safe_end.putIndex _ _)
    refine ⟨t,load.seq (sel.seq (add.seq inc)),inc.safe_end,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp [t,w1,wi,s1,cnt]
    · simp [t,w1,wi,s1,size]
    · simp [t,w1,wi,s1,cur,Nat.add_assoc]
    · simpa [t,w1,o4] using width'
    · simpa [t,w1] using addPos
    · simpa [t,w1] using wone
    · intro i io i3 i4 i5
      simpa [t,w1,i4,wkeep i io,s1,i3] using frame i io i3 i4 i5
    · intro i i1 i2
      simpa [t,w1,i1,i2,wi,s1] using idx i i1 i2
  obtain ⟨t,loop,_,_,_,cur,ans,pos,one,frame,idx⟩ := Block.Eval.forRange_invariant_exact 2 0 k 5 I z
    e3.safe_end init (fun _ _ h => ⟨h.1,h.2.1,h.2.2.1⟩) body
  refine ⟨t,?_,by simpa only [Nat.mod_eq_of_lt ha] using ans,pos,one,cur,frame,idx⟩
  simpa only [widthScanBlock,show 1+(1+(1+(k*(5+3)+2)))=8*k+5 by omega] using e1.seq (e2.seq (e3.seq loop))

end Compression
end LinearProgramming
end Optimization
end OAI
