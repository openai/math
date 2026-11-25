import OAI.Optimization.LinearProgramming.Compression.BinaryUnpackLayout

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

private def unpackDigitBody : Block := .seq (.op (.addrLoad 0 1)) <| .seq (.op (.decr 0 0)) <|
  .seq (.op (.addrStore 2 0)) <| .seq (.op (.incr 1 1)) <| .seq (.op (.incr 1 1)) <|
  .seq (.op (.incr 2 2)) <| .seq (.op (.const 6 1)) <| .seq (.op (.sub 5 5 6)) (.op (.const 6 0))

def compactDoubledWords : Block := .seq (.op (.addrConst 1 6)) <| .seq (.op (.addrConst 2 3)) <|
  .seq (.op (.const 6 0)) (.loop (.scalarLT 6 5) unpackDigitBody)

structure CompactPacket (m : Memory ℚ) (n d sign : ℕ) (digit : ℕ → ℕ) : Prop where
  pointer : m.index 1 = endOfDoubledWords n d
  numeratorWidth : m.index (endOfDoubledWords n d)=n
  denominatorWidth : m.index (endOfDoubledWords n d+1)=d
  negative : m.index (endOfDoubledWords n d+2)=sign
  words : ∀ i < n+d, m.index (3+i)=digit i

private structure ScanInvariant (P : ℚ → Prop) (m : Memory ℚ) (n d sign : ℕ) (digit : ℕ → ℕ)
    (j : ℕ) (s : Memory ℚ) : Prop where
  safe : s.AllData P
  read : s.index 1=6+2*j
  write : s.index 2=3+j
  remaining : s.data 5=((n+d-j:ℕ):ℚ)
  zero : s.data 6=0
  nw : s.index (endOfDoubledWords n d)=n
  dw : s.index (endOfDoubledWords n d+1)=d
  sg : s.index (endOfDoubledWords n d+2)=sign
  unread : ∀ i, j ≤ i → i < n+d → s.index (6+2*i)=2*digit i
  written : ∀ i < j, s.index (3+i)=digit i
  frame : ∀ i, i ≠ 5 → i ≠ 6 → s.data i=m.data i

private theorem unpackDigitBody_spec (m : Memory ℚ) (n d sign : ℕ) (digit : ℕ → ℕ) (j : ℕ)
    (s : Memory ℚ) {P : ℚ → Prop} (h : ScanInvariant P m n d sign digit j s) (hj : j < n+d)
    (bits : ∀ i < n+d, digit i ≤ 1) (small : ∀ i : ℕ, i ≤ n+d → P (i:ℚ)) :
    ∃ t, Block.Eval (Memory.AllData P) unpackDigitBody s 9 t ∧ ScanInvariant P m n d sign digit (j+1) t := by
  let H := endOfDoubledWords n d
  have lo : 3+j < H := by dsimp [H,endOfDoubledWords]; omega
  let a := s.putIndex 0 (2*digit j)
  let b := a.putIndex 0 (digit j)
  let c := b.putIndex (3+j) (digit j)
  let w := c.putIndex 1 (6+2*j+1)
  let z := w.putIndex 1 (6+2*(j+1))
  let u := z.putIndex 2 (3+(j+1))
  let v := u.putData 6 1
  let p := v.putData 5 ((n+d-(j+1):ℕ):ℚ)
  let t := p.putData 6 0
  have read : s.index (s.index 1)=2*digit j := by rw [h.read,h.unread j le_rfl hj]
  have vdigit := bits j hj
  have scaled : a.index 0 - 1= digit j := by simp [a]; omega
  have dest : b.index 2=3+j := by simp [b,a,h.write]
  have value : b.index 0=digit j := Memory.putIndex_same ..
  have cptr : c.index 1=6+2*j := by simp [c,b,a,show 1 ≠ 3+j by omega,h.read]
  have wptr : w.index 1+1=6+2*(j+1) := by simp [w]; omega
  have zptr : z.index 2+1=3+(j+1) := by simp [z,w,c,b,a,show 2 ≠ 3+j by omega,h.write]; omega
  have minus : v.data 5 - v.data 6=((n+d-(j+1):ℕ):ℚ) := by
    simp only [v,Memory.putData_same]
    change s.data 5-1=_
    rw [h.remaining,show n+d-j=n+d-(j+1)+1 by omega]; push_cast; ring
  have zero : P (0:ℚ) := by simpa using small 0 (by omega)
  have one : P (1:ℚ) := by simpa using small 1 (by omega)
  have e1 : Block.Eval (Memory.AllData P) (.op (.addrLoad 0 1)) s 1 a := by
    simpa only [a,read] using Block.Eval.op_addrLoad s 0 1 h.safe (h.safe.putIndex _ _)
  have e2 : Block.Eval (Memory.AllData P) (.op (.decr 0 0)) a 1 b := by
    simpa only [b,scaled] using Block.Eval.op_decr a 0 0 e1.safe_end (e1.safe_end.putIndex _ _)
  have e3 : Block.Eval (Memory.AllData P) (.op (.addrStore 2 0)) b 1 c := by
    simpa only [c,dest,value] using Block.Eval.op_addrStore b 2 0 e2.safe_end (e2.safe_end.putIndex _ _)
  have e4 : Block.Eval (Memory.AllData P) (.op (.incr 1 1)) c 1 w := by
    simpa only [w,cptr] using Block.Eval.op_incr c 1 1 e3.safe_end (e3.safe_end.putIndex _ _)
  have e5 : Block.Eval (Memory.AllData P) (.op (.incr 1 1)) w 1 z := by
    simpa only [z,wptr] using Block.Eval.op_incr w 1 1 e4.safe_end (e4.safe_end.putIndex _ _)
  have e6 : Block.Eval (Memory.AllData P) (.op (.incr 2 2)) z 1 u := by
    simpa only [u,zptr] using Block.Eval.op_incr z 2 2 e5.safe_end (e5.safe_end.putIndex _ _)
  have e7 := Block.Eval.op_const u 6 1 e6.safe_end (e6.safe_end.putData 6 one)
  have e8 : Block.Eval (Memory.AllData P) (.op (.sub 5 5 6)) v 1 p := by
    simpa only [p,minus] using Block.Eval.op_sub v 5 5 6 e7.safe_end (e7.safe_end.putData _ (minus ▸ small _ (by omega)))
  have e9 := Block.Eval.op_const p 6 0 e8.safe_end (e8.safe_end.putData 6 zero)
  have same (i : ℕ) (big : 3 ≤ i) (other : i ≠ 3+j) : t.index i=s.index i := by
    simp [t,p,v,u,z,w,c,b,a,show i ≠ 0 by omega,show i ≠ 1 by omega,show i ≠ 2 by omega,other]
  refine ⟨t,e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq e9))))))),
    e9.safe_end,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [t,p,v,u,z]
  · simp [t,p,v,u]
  · simp [t,p]
  · simp [t]
  · exact (same H (by omega) (by omega)).trans h.nw
  · exact (same (H+1) (by omega) (by omega)).trans h.dw
  · exact (same (H+2) (by omega) (by omega)).trans h.sg
  · intro i hi hin; exact (same _ (by omega) (by omega)).trans (h.unread i (by omega) hin)
  · intro i hi
    by_cases eq : i=j
    · subst i; simp [t,p,v,u,z,w,c,show 3+j ≠ 1 by omega,show 3+j ≠ 2 by omega]
    · exact (same _ (by omega) (by omega)).trans (h.written i (by omega))
  · intro i i5 i6; simpa [t,p,v,u,z,w,c,b,a,i5,i6] using h.frame i i5 i6

theorem compactDoubledWords_spec (m : Memory ℚ) (n d sign : ℕ) (digit : ℕ → ℕ) {P : ℚ → Prop}
    (safe : m.AllData P) (pack : StagedPacket m n d sign digit) (bits : ∀ i < n+d,digit i ≤ 1)
    (small : ∀ i : ℕ, i ≤ n+d → P (i:ℚ)) :
    ∃ t, Block.Eval (Memory.AllData P) compactDoubledWords m (11*(n+d)+4) t ∧
      CompactPacket t n d sign digit ∧ ∀ i, i ≠ 5 → i ≠ 6 → t.data i=m.data i := by
  let H := endOfDoubledWords n d
  have hH : 6 ≤ H := by dsimp [H,endOfDoubledWords]; omega
  have zero : P (0:ℚ) := by simpa using small 0 (by omega)
  let a := m.putIndex 1 6
  let b := a.putIndex 2 3
  let c := b.putData 6 0
  have e1 := Block.Eval.op_addrConst m 1 6 safe (safe.putIndex _ _)
  have e2 := Block.Eval.op_addrConst a 2 3 e1.safe_end (e1.safe_end.putIndex _ _)
  have e3 := Block.Eval.op_const b 6 0 e2.safe_end (e2.safe_end.putData _ zero)
  have ci (i : ℕ) (hi : 3 ≤ i) : c.index i=m.index i := by simp [c,b,a,show i ≠ 1 by omega,show i ≠ 2 by omega]
  have start : ScanInvariant P m n d sign digit 0 c := by
    refine ⟨e3.safe_end,by simp [c,b,a],by simp [c,b],?_,by simp [c],(ci H (by omega)).trans pack.numeratorWidth,
      (ci (H+1) (by omega)).trans pack.denominatorWidth,(ci (H+2) (by omega)).trans pack.negative,?_,by omega,?_⟩
    · exact (Memory.putData_ne b (by decide : 5 ≠ 6) (0 : ℚ)).trans pack.count
    · intro i _ hi; exact (ci _ (by omega)).trans (pack.words i hi)
    · intro i _ i6; simp [c,b,a,i6]
  have advance (j : ℕ) (hj : j < n+d) (s : Memory ℚ) (h : ScanInvariant P m n d sign digit j s) :
      (Cond.scalarLT 6 5).test s=true ∧ ∃ t, Block.Eval (Memory.AllData P) unpackDigitBody s 9 t ∧ ScanInvariant P m n d sign digit (j+1) t := by
    refine ⟨by simp [Cond.test,h.zero,h.remaining,Nat.sub_pos_of_lt hj],unpackDigitBody_spec m n d sign digit j s h hj bits small⟩
  have stop (s : Memory ℚ) (h : ScanInvariant P m n d sign digit (n+d) s) : (Cond.scalarLT 6 5).test s=false ∧ s.AllData P :=
    ⟨by simp [Cond.test,h.zero,h.remaining],h.safe⟩
  obtain ⟨t,run,result⟩ := Block.Eval.loop_invariant_exact (ScanInvariant P m n d sign digit) c (n+d) 9 start advance stop
  refine ⟨t,?_,⟨result.read,result.nw,result.dw,result.sg,result.written⟩,result.frame⟩
  simpa only [compactDoubledWords,show 1+(1+(1+((n+d)*(9+2)+1)))=11*(n+d)+4 by omega] using e1.seq (e2.seq (e3.seq run))

end Compression
end LinearProgramming
end Optimization
end OAI
