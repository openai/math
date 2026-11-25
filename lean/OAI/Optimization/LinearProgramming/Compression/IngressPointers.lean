import OAI.Optimization.LinearProgramming.Compression.IngressIndex

/-! Finish the low-register bootstrap and expose the buffered request through registers
40 through 43. All header sizes are computed by address instructions. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Ingress

open RAM
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def prepareEnd : Block :=
  .seq (.op (.addrCopy 3 0)) (.seq (walk true 3 68) (.op (.addrConst 2 4)))

theorem prepareEnd_spec (P : K → Prop) (s : Memory K) (len : ℕ)
    (h : s.index 0=64+len+4) (hs : Good P s) :
    ∃ t, Block.Eval (Good P) prepareEnd s 70 t ∧ t.data=s.data ∧ t.index 3=len ∧ t.index 2=4 ∧
      ∀ i, i ≠ 2 → i ≠ 3 → t.index i=s.index i := by
  let a := s.putIndex 3 (s.index 0)
  have ea : Block.Eval (Good P) (.op (.addrCopy 3 0)) s 1 a := Block.Eval.op_addrCopy _ _ _ hs hs
  obtain ⟨b,eb,bd,b3,bf⟩ := walk_spec P a true 3 68 ea.safe_end
  let t := b.putIndex 2 4
  have et : Block.Eval (Good P) (.op (.addrConst 2 4)) b 1 t :=
    Block.Eval.op_addrConst _ _ _ eb.safe_end eb.safe_end
  refine ⟨t,ea.seq (eb.seq et),bd,?_,by simp [t],?_⟩
  · simp [a,h] at b3
    simp [t,b3]
  · intro i i2 i3; simpa [t,a,i2,i3] using bf i i3

def exposeBuffer : Block :=
  .seq (.op (.addrCopy 40 3)) (.seq (walk false 40 64)
    (.seq (.op (.addrCopy 41 3)) (.seq (.op (.addrLoad 43 40)) (.seq (.op (.addrCopy 0 40))
    (.seq (.op (.incr 0 0)) (.seq (.op (.addrLoad 42 0)) (.op (.add 3 1 2))))))))

theorem exposeBuffer_spec (P : K → Prop) (s : Memory K) (len : ℕ) (h3 : s.index 3=len)
    (hs : Good P s) (hn : P (s.data 1+s.data 2)) :
    ∃ t, Block.Eval (Good P) exposeBuffer s 71 t ∧ t.index 40=64+len ∧ t.index 41=len ∧
      t.index 42=s.index (64+len+1) ∧ t.index 43=s.index (64+len) ∧
      (∀ (i : ℕ), 64 ≤ i → t.index i=s.index i) ∧ t.data 3=s.data 1+s.data 2 ∧
      ∀ i, i ≠ 3 → t.data i=s.data i := by
  let a := s.putIndex 40 (s.index 3)
  have ea : Block.Eval (Good P) (.op (.addrCopy 40 3)) s 1 a := Block.Eval.op_addrCopy _ _ _ hs hs
  obtain ⟨b,eb,bd,b40,bf⟩ := walk_spec P a false 40 64 ea.safe_end
  have bi i : b.index i=(if i=40 then 64+len else s.index i) := by
    by_cases hi : i=40
    · subst i; simpa [a,h3,Nat.add_comm] using b40
    · simpa [hi,a] using bf i hi
  let c := b.putIndex 41 (b.index 3)
  let d := c.putIndex 43 (c.index (c.index 40))
  let e := d.putIndex 0 (d.index 40)
  let f := e.putIndex 0 (e.index 0+1)
  let g := f.putIndex 42 (f.index (f.index 0))
  let t := g.putData 3 (g.data 1+g.data 2)
  have eh : Good P b := eb.safe_end
  have ht : Good P t := safeWrite (m := g) eh (by simpa [g,f,e,d,c,bd,a] using hn)
  have ec : Block.Eval (Good P) (.op (.addrCopy 41 3)) b 1 c := Block.Eval.op_addrCopy _ _ _ eh eh
  have ed : Block.Eval (Good P) (.op (.addrLoad 43 40)) c 1 d := Block.Eval.op_addrLoad _ _ _ eh eh
  have ee : Block.Eval (Good P) (.op (.addrCopy 0 40)) d 1 e := Block.Eval.op_addrCopy _ _ _ eh eh
  have ef : Block.Eval (Good P) (.op (.incr 0 0)) e 1 f := Block.Eval.op_incr _ _ _ eh eh
  have eg : Block.Eval (Good P) (.op (.addrLoad 42 0)) f 1 g := Block.Eval.op_addrLoad _ _ _ eh eh
  have et : Block.Eval (Good P) (.op (.add 3 1 2)) g 1 t := Block.Eval.op_add _ _ _ _ eh ht
  refine ⟨t,ea.seq (eb.seq (ec.seq (ed.seq (ee.seq (ef.seq (eg.seq et)))))),?_,?_,?_,?_,?_,?_,?_⟩
  · simp [t,g,f,e,d,c,bi]
  · simp [t,g,f,e,d,c,bi,h3]
  · simp (disch := omega) [t,g,f,e,d,c,bi]
    omega
  · simp (disch := omega) [t,g,f,e,d,c,bi]
    omega
  · intro i hi
    simp (disch := omega) [t,g,f,e,d,c,bi]
    omega
  · simp [t,g,f,e,d,c,bd,a]
  · intro i hi; simp [t,g,f,e,d,c,bd,a,hi]

end Ingress
end Compression
end LinearProgramming
end Optimization
end OAI
