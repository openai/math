import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import OAI.Optimization.LinearProgramming.Compression.IngressIndex
import OAI.Optimization.LinearProgramming.Compression.UniformIndex
import OAI.Optimization.LinearProgramming.RAM.StrideCopy

/-! Save the service's live scalar tape in the odd physical cells of a call frame.
The original and destination overlap, so data is copied in decreasing source order.
Scalar 6 is the sole scratch value. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ServiceSave

open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Register 7 is the end of the live scalar tape; registers 8 and 9 become backward
source and odd-destination cursors, and 12 becomes the number of words above the header. -/
private def pointers : Block :=
  .seq (.op (.addrConst 24 0)) (.seq (.op (.addrConst 25 1))
    (.seq (cellAddress 9 10 11 7 7 25 24) (.seq (.op (.decr 9 9))
    (.seq (.op (.decr 8 7)) (.seq (.op (.addrCopy 12 7)) (Ingress.walk true 12 7))))))

private theorem pointers_spec (P : K → Prop) (s : Memory K) (L : ℕ) (hL : s.index 7=L)
    (hs : ∀ i,P (s.data i)) :
    ∃ t, Block.Eval (fun m => ∀ i,P (m.data i)) pointers s (4*L+22) t ∧
      t.data=s.data ∧ t.index 8=L-1 ∧ t.index 9=2*L-1 ∧ t.index 12=L-7 ∧
      ∀ i, i∉[8,9,10,11,12,24,25] → t.index i=s.index i := by
  let safe := fun m : Memory K => ∀ i,P (m.data i)
  let a := s.putIndex 24 0
  let b := a.putIndex 25 1
  have ea : Block.Eval safe (.op (.addrConst 24 0)) s 1 a := Block.Eval.op_addrConst _ _ _ hs hs
  have eb : Block.Eval safe (.op (.addrConst 25 1)) a 1 b := Block.Eval.op_addrConst _ _ _ hs hs
  have b7 : b.index 7=L := by simp [b,a,hL]
  have b24 : b.index 24=0 := by simp [b,a]
  have b25 : b.index 25=1 := by simp [b]
  obtain ⟨c,ec,cd,cf,c9⟩ := cellAddress_spec (K := K) (fun f => ∀ i,P (f i)) b hs
    9 10 11 7 7 25 24 (by simp [CellScratchOK])
  have c7 := (cf 7 (by decide) (by decide) (by decide)).trans b7
  have cv : c.index 9=2*L := by simp [b7,b24,b25] at c9; omega
  let d := c.putIndex 9 (c.index 9-1)
  let e := d.putIndex 8 (d.index 7-1)
  let f := e.putIndex 12 (e.index 7)
  have ed : Block.Eval safe (.op (.decr 9 9)) c 1 d := Block.Eval.op_decr _ _ _ ec.safe_end ec.safe_end
  have ee : Block.Eval safe (.op (.decr 8 7)) d 1 e := Block.Eval.op_decr _ _ _ ec.safe_end ec.safe_end
  have ef : Block.Eval safe (.op (.addrCopy 12 7)) e 1 f := Block.Eval.op_addrCopy _ _ _ ec.safe_end ec.safe_end
  obtain ⟨t,et,td,t12,tf⟩ := Ingress.walk_spec P f true 12 7 ef.safe_end
  refine ⟨t,?_,td.trans cd,?_,?_,?_,?_⟩
  · have run := ea.seq (eb.seq (ec.seq (ed.seq (ee.seq (ef.seq et)))))
    simp only [b7,b25,b24,one_mul,Nat.mul_zero,Nat.add_zero] at run
    unfold pointers
    convert run using 1
    omega
  · simpa [f,e,d,c7] using tf 8 (by decide)
  · simpa [f,e,d,cv] using tf 9 (by decide)
  · simpa [f,e,d,c7] using t12
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
    obtain ⟨i8,i9,i10,i11,i12,i24,i25⟩ := hi
    simpa [f,e,d,b,a,i8,i9,i12,i24,i25,cf i i9 i10 i11] using tf i i12

private def move : Block := StrideCopy.block true 8 9 11 12 6 1 2

private theorem move_spec (P : K → Prop) (s : Memory K) (L : ℕ) (hL : 7 ≤ L)
    (h8 : s.index 8=L-1) (h9 : s.index 9=2*L-1) (h12 : s.index 12=L-7)
    (hs : ∀ i,P (s.data i)) :
    ∃ t, Block.Eval (fun m => ∀ i,P (m.data i)) move s (8*(L-7)+2) t ∧
      (∀ i, 7 ≤ i → i < L → t.data (2*i+1)=s.data i) ∧
      (∀ i, i < 6 → t.data i=s.data i) ∧
      ∀ i, i ≠ 8 → i ≠ 9 → i ≠ 11 → t.index i=s.index i := by
  have src j : StrideCopy.address true (s.index 8) 1 j = L-1-j := by
    simp [StrideCopy.address,StrideCopy.move,h8]
  have dst j : StrideCopy.address true (s.index 9) 2 j = 2*L-1-2*j := by
    simp [StrideCopy.address,StrideCopy.move,h9]
  obtain ⟨t,run,written,frame,_,_,_,idx⟩ := StrideCopy.block_correct P s true 8 9 11 12 6 1 2
    (L-7) hs h12 (by decide) (by decide) (by intro _; rw [h9]; omega)
    (by intro j hj; rw [src]; omega) (by intro j hj; rw [dst]; omega)
    (by intro j k hj hk; rw [dst,src]; omega)
  have scalarInvariant : Memory.AllData P = (fun m : Memory K => ∀ i, P (m.data i)) := by
    funext m
    rfl
  rw [scalarInvariant] at run
  refine ⟨t,by simpa [move,Nat.mul_comm] using run,?_,?_,idx⟩
  · intro i lo hi
    have w := written (L-1-i) (by omega)
    rw [dst,src] at w
    have wd : 2*L-1-2*(L-1-i)=2*i+1 := by omega
    have ws : L-1-(L-1-i)=i := by omega
    simpa only [wd,ws] using w
  · intro i hi
    exact frame i (by omega) (by intro j hj; rw [dst]; omega)

/-- Save four overlapping header words only after the high scalar tape is safe. The
order 4,3,2,1 prevents writing to header 3 before saving its old value. -/
private def header : Block :=
  .seq (.op (.copy 9 4)) (.seq (.op (.copy 7 3)) (.seq (.op (.copy 5 2)) (.op (.copy 3 1))))

private theorem header_spec (P : K → Prop) (s : Memory K) (hs : ∀ i,P (s.data i)) :
    ∃ t, Block.Eval (fun m => ∀ i,P (m.data i)) header s 4 t ∧ t.index=s.index ∧
      (∀ i, 1 ≤ i → i ≤ 4 → t.data (2*i+1)=s.data i) ∧
      ∀ i, 10 ≤ i → t.data i=s.data i := by
  let a := s.putData 9 (s.data 4)
  let b := a.putData 7 (a.data 3)
  let c := b.putData 5 (b.data 2)
  let t := c.putData 3 (c.data 1)
  have ha : Ingress.Good P a := Ingress.safeWrite hs (hs _)
  have hb : Ingress.Good P b := Ingress.safeWrite ha (ha _)
  have hc : Ingress.Good P c := Ingress.safeWrite hb (hb _)
  have ht : Ingress.Good P t := Ingress.safeWrite hc (hc _)
  have ea : Block.Eval (Ingress.Good P) (.op (.copy 9 4)) s 1 a := Block.Eval.op_copy _ _ _ hs ha
  have eb : Block.Eval (Ingress.Good P) (.op (.copy 7 3)) a 1 b := Block.Eval.op_copy _ _ _ ha hb
  have ec : Block.Eval (Ingress.Good P) (.op (.copy 5 2)) b 1 c := Block.Eval.op_copy _ _ _ hb hc
  have et : Block.Eval (Ingress.Good P) (.op (.copy 3 1)) c 1 t := Block.Eval.op_copy _ _ _ hc ht
  refine ⟨t,ea.seq (eb.seq (ec.seq et)),rfl,?_,?_⟩
  · intro i lo hi
    interval_cases i <;> norm_num [t,c,b,a]
  · intro i hi; simp (disch := omega) [t,c,b,a]

def saveLive : Block := .seq pointers (.seq move header)

/-- The magnitude vector, staged candidate, two matrices, all sorted slots and the four
persistent header scalars can all be retained in the caller frame of an arbitrary ROM. -/
theorem saveLive_spec (P : K → Prop) (s : Memory K) (L : ℕ) (hL : 7 ≤ L) (h7 : s.index 7=L)
    (hs : ∀ i,P (s.data i)) :
    ∃ t, Block.Eval (fun m => ∀ i,P (m.data i)) saveLive s (4*L+22+(8*(L-7)+2+4)) t ∧
      (∀ i, 1 ≤ i → i < L → i ≠ 5 → i ≠ 6 → t.data (2*i+1)=s.data i) ∧
      ∀ i, i∉[8,9,10,11,12,24,25] → t.index i=s.index i := by
  obtain ⟨a,ea,ad,h8,h9,h12,af⟩ := pointers_spec P s L h7 hs
  obtain ⟨b,eb,high,low,bi⟩ := move_spec P a L hL h8 h9 h12 ea.safe_end
  obtain ⟨t,et,ti,th,tf⟩ := header_spec P b eb.safe_end
  refine ⟨t,ea.seq (eb.seq et),?_,?_⟩
  · intro i one hi i5 i6
    by_cases sm : i ≤ 4
    · exact (th _ one sm).trans ((low _ (by omega)).trans (congrFun ad _))
    · exact (tf _ (by omega)).trans ((high _ (by omega) hi).trans (congrFun ad _))
  · intro i h
    have h' := h
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h'
    exact (congrFun ti i).trans ((bi i h'.1 h'.2.1 h'.2.2.2.1).trans (af i h))

end ServiceSave
end Compression
end LinearProgramming
end Optimization
end OAI
