import OAI.Optimization.LinearProgramming.RAM.Loops

/-! Bootstrapping scratch registers when the incoming variable-length request occupies the
low address registers. No unread address register is used as scratch. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Ingress

open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def Good (P : K → Prop) (s : Memory K) := ∀ i, P (s.data i)

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem safeWrite {P : K → Prop} {m : Memory K} {i : ℕ} {x : K} (hm : Good P m) (hx : P x) :
    Good P (m.putData i x) := by
  intro j
  by_cases h : j=i
  · simpa [h] using hx
  · simpa [h] using hm j

/-- Save the row count before using scalar registers 0 and 1 as a two-cell lookup table
for the input tag. This frees address register 0 without losing any request word. -/
def saveTag : Block :=
  .seq (.op (.copy 5 1)) (.seq (.op (.const 0 0)) (.seq (.op (.const 1 1))
    (.seq (.op (.load 6 0)) (.seq (.op (.copy 1 5)) (.seq (.op (.const 3 1))
      (.seq (.op (.const 5 0)) (.op (.addrConst 0 0))))))))

theorem saveTag_spec (P : K → Prop) (s : Memory K) (tag : ℕ)
    (hbit : tag ≤ 1) (htag : s.index 0=tag) (hs : Good P s) (h0 : P 0) (h1 : P 1) :
    ∃ t, Block.Eval (Good P) saveTag s 8 t ∧ t.data 0=0 ∧ t.data 3=1 ∧ t.data 5=0 ∧
      t.data 6=(tag : K) ∧ t.index 0=0 ∧ (∀ i, i≠0 → t.index i=s.index i) ∧
      ∀ i, i≠0 → i≠3 → i≠5 → i≠6 → t.data i=s.data i := by
  let a := s.putData 5 (s.data 1)
  let b := a.putData 0 ((0 : ℚ) : K)
  let c := b.putData 1 ((1 : ℚ) : K)
  let d := c.putData 6 (c.data (c.index 0))
  let e := d.putData 1 (d.data 5)
  let f := e.putData 3 ((1 : ℚ) : K)
  let g := f.putData 5 ((0 : ℚ) : K)
  let t := g.putIndex 0 0
  have ha : Good P a := safeWrite hs (hs _)
  have hb : Good P b := safeWrite ha (by simpa using h0)
  have hc : Good P c := safeWrite hb (by simpa using h1)
  have hd : Good P d := safeWrite hc (hc _)
  have he : Good P e := safeWrite hd (hd _)
  have hf : Good P f := safeWrite he (by simpa using h1)
  have hg : Good P g := safeWrite hf (by simpa using h0)
  have ea : Block.Eval (Good P) (.op (.copy 5 1)) s 1 a := Block.Eval.op_copy _ _ _ hs ha
  have eb : Block.Eval (Good P) (.op (.const 0 0)) a 1 b := Block.Eval.op_const _ _ _ ha hb
  have ec : Block.Eval (Good P) (.op (.const 1 1)) b 1 c := Block.Eval.op_const _ _ _ hb hc
  have ed : Block.Eval (Good P) (.op (.load 6 0)) c 1 d := Block.Eval.op_load _ _ _ hc hd
  have ee : Block.Eval (Good P) (.op (.copy 1 5)) d 1 e := Block.Eval.op_copy _ _ _ hd he
  have ef : Block.Eval (Good P) (.op (.const 3 1)) e 1 f := Block.Eval.op_const _ _ _ he hf
  have eg : Block.Eval (Good P) (.op (.const 5 0)) f 1 g := Block.Eval.op_const _ _ _ hf hg
  have et : Block.Eval (Good P) (.op (.addrConst 0 0)) g 1 t := Block.Eval.op_addrConst _ _ _ hg hg
  refine ⟨t, ea.seq (eb.seq (ec.seq (ed.seq (ee.seq (ef.seq (eg.seq et)))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [t,g,f,e,d,c,b]
  · simp [t,g,f]
  · simp [t,g]
  · have ht : tag=0 ∨ tag=1 := by omega
    rcases ht with rfl | rfl <;> simp [t,g,f,e,d,c,b,a,htag]
  · simp [t]
  · intro j hj; simp [t,g,f,e,d,c,b,a,hj]
  · intro j j0 j3 j5 j6
    by_cases j1 : j=1
    · subst j
      simp [t,g,f,e,d,c,b,a]
    · simp [t,g,f,e,d,c,b,a,j0,j1,j3,j5,j6]

/-- Move the order to scalar register 5, leaving address register 1 zero and every
incoming row/column register (addresses 2 and above) intact. -/
def consumeOrder : Block :=
  .loop (.addrLT 0 1) (.seq (.op (.decr 1 1)) (.op (.add 5 5 3)))

theorem consumeOrder_spec (P : K → Prop) (s : Memory K) (k : ℕ)
    (h0 : s.index 0=0) (h1 : s.index 1=k) (h5 : s.data 5=0) (h3 : s.data 3=1)
    (hs : Good P s) (hv : ∀ i≤k, P (i : K)) :
    ∃ t, Block.Eval (Good P) consumeOrder s (4*k+1) t ∧ t.index 1=0 ∧ t.data 5=(k : K) ∧
      (∀ i, i≠1 → t.index i=s.index i) ∧ ∀ i, i≠5 → t.data i=s.data i := by
  let I := fun (j : ℕ) (m : Memory K) => Good P m ∧ m.index 1=k-j ∧ m.data 5=(j : K) ∧
    (∀ i, i≠1 → m.index i=s.index i) ∧ ∀ i, i≠5 → m.data i=s.data i
  have base : I 0 s := ⟨hs,by simpa using h1,by simpa using h5,fun _ _ => rfl,fun _ _ => rfl⟩
  have step (j : ℕ) (hj : j<k) (m : Memory K) (h : I j m) :
      (Cond.addrLT 0 1).test m = true ∧ ∃ t, Block.Eval (Good P)
        (.seq (.op (.decr 1 1)) (.op (.add 5 5 3))) m 2 t ∧ I (j+1) t := by
    obtain ⟨hm,h1',h5',hfi,hfd⟩ := h
    have hz := (hfi 0 (by decide)).trans h0
    have hone := (hfd 3 (by decide)).trans h3
    refine ⟨by simp [Cond.test,hz,h1',hj],?_⟩
    let a := m.putIndex 1 (m.index 1-1)
    let t := a.putData 5 (a.data 5+a.data 3)
    have val : a.data 5+a.data 3=((j+1 : ℕ) : K) := by simp [a,h5',hone]
    have ht : Good P t := safeWrite hm (val ▸ hv _ hj)
    have ea : Block.Eval (Good P) (.op (.decr 1 1)) m 1 a := Block.Eval.op_decr _ _ _ hm hm
    have et : Block.Eval (Good P) (.op (.add 5 5 3)) a 1 t := Block.Eval.op_add _ _ _ _ hm ht
    refine ⟨t,ea.seq et,ht, ?_,by simp [t,val],?_,?_⟩
    · simp [t,a,h1',Nat.sub_sub]
    · intro i hi; simpa [t,a,hi] using hfi i hi
    · intro i hi; simpa [t,a,hi] using hfd i hi
  have stop (m : Memory K) (h : I k m) : (Cond.addrLT 0 1).test m = false ∧ Good P m := by
    obtain ⟨hm,h1',_,hfi,_⟩ := h
    exact ⟨by simp [Cond.test,h1',(hfi 0 (by decide)).trans h0],hm⟩
  obtain ⟨t,he,_,hz,hk,ha,hf⟩ := Block.Eval.loop_invariant_exact I s k 2 base step stop
  exact ⟨t, by simpa [consumeOrder,Nat.mul_comm] using he, by simpa using hz, hk, ha, hf⟩

/-- Construct the fresh address bank base at `66 + 2 * k` and recreate the original
order in address register 1. Both loops used for bootstrap touch no index above 1. -/
def prepareFreshAddress : Block :=
  .seq (.op (.addrConst 0 66)) (.loop (.scalarLT 0 5)
    (.seq (.op (.add 0 0 3)) (.seq (.op (.incr 1 1)) (.seq (.op (.incr 0 0)) (.op (.incr 0 0))))))

theorem prepareFreshAddress_spec (P : K → Prop) (s : Memory K) (k : ℕ)
    (h1 : s.index 1=0) (h0 : s.data 0=0) (h5 : s.data 5=(k : K)) (h3 : s.data 3=1)
    (hs : Good P s) (hv : ∀ i≤k, P (i : K)) :
    ∃ t, Block.Eval (Good P) prepareFreshAddress s (6*k+2) t ∧
      t.index 0=66+2*k ∧ t.index 1=k ∧ t.data 0=(k : K) ∧
      (∀ i, i≠0 → i≠1 → t.index i=s.index i) ∧ ∀ i, i≠0 → t.data i=s.data i := by
  let a := s.putIndex 0 66
  have ea : Block.Eval (Good P) (.op (.addrConst 0 66)) s 1 a := Block.Eval.op_addrConst _ _ _ hs hs
  let I := fun (j : ℕ) (m : Memory K) => Good P m ∧ m.index 0=66+2*j ∧ m.index 1=j ∧
    m.data 0=(j:K) ∧ (∀ i, i≠0 → i≠1 → m.index i=s.index i) ∧ ∀ i, i≠0 → m.data i=s.data i
  have base : I 0 a := by
    refine ⟨hs,by simp [a],by simpa [a] using h1,by simpa [a] using h0,?_,fun _ _ => rfl⟩
    intro i hi _; simp [a,hi]
  have step (j : ℕ) (hj : j<k) (m : Memory K) (h : I j m) :
      (Cond.scalarLT 0 5).test m = true ∧ ∃ t, Block.Eval (Good P)
        (.seq (.op (.add 0 0 3)) (.seq (.op (.incr 1 1)) (.seq (.op (.incr 0 0)) (.op (.incr 0 0)))))
        m 4 t ∧ I (j+1) t := by
    obtain ⟨hm,h0',h1',hv',hfi,hfd⟩ := h
    have hk := (hfd 5 (by decide)).trans h5
    have hone := (hfd 3 (by decide)).trans h3
    refine ⟨by simpa [Cond.test,hv',hk] using hj,?_⟩
    let a := m.putData 0 (m.data 0+m.data 3)
    let b := a.putIndex 1 (a.index 1+1)
    let c := b.putIndex 0 (b.index 0+1)
    let t := c.putIndex 0 (c.index 0+1)
    have val : m.data 0+m.data 3=((j+1:ℕ):K) := by simp [hv',hone]
    have ha : Good P a := safeWrite hm (val ▸ hv _ hj)
    have ea : Block.Eval (Good P) (.op (.add 0 0 3)) m 1 a := Block.Eval.op_add _ _ _ _ hm ha
    have eb : Block.Eval (Good P) (.op (.incr 1 1)) a 1 b := Block.Eval.op_incr _ _ _ ha ha
    have ec : Block.Eval (Good P) (.op (.incr 0 0)) b 1 c := Block.Eval.op_incr _ _ _ ha ha
    have et : Block.Eval (Good P) (.op (.incr 0 0)) c 1 t := Block.Eval.op_incr _ _ _ ha ha
    refine ⟨t,ea.seq (eb.seq (ec.seq et)),ha,?_,by simp [t,c,b,a,h1'],by simp [t,c,b,a,val],?_,?_⟩
    · simp [t,c,b,a,h0']; omega
    · intro i hi0 hi1; simpa [t,c,b,a,hi0,hi1] using hfi i hi0 hi1
    · intro i hi; simpa [t,c,b,a,hi] using hfd i hi
  have stop (m : Memory K) (h : I k m) : (Cond.scalarLT 0 5).test m = false ∧ Good P m := by
    obtain ⟨hm,_,_,hv',_,hfd⟩ := h
    exact ⟨by simp [Cond.test,hv',(hfd 5 (by decide)).trans h5],hm⟩
  obtain ⟨t,et,_,hb,ho,hv',hfi,hfd⟩ := Block.Eval.loop_invariant_exact I a k 4 base step stop
  refine ⟨t,?_,hb,ho,hv',hfi,hfd⟩
  unfold prepareFreshAddress
  convert ea.seq et using 1; omega

end Ingress
end Compression
end LinearProgramming
end Optimization
end OAI
