import OAI.Optimization.LinearProgramming.Compression.IngressCore

/-! Native forward copy of the unread suffix after the first four address registers
have been released as scratch. Its destination lies above the entire original tape. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Ingress

open RAM
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def copyBody : Block :=
  .seq (.op (.addrLoad 1 2)) (.seq (.op (.addrStore 0 1))
    (.seq (.op (.incr 2 2)) (.op (.incr 0 0))))

private theorem body_spec (P : K → Prop) (s : Memory K) (d r : ℕ) (hd : 4≤d)
    (h0 : s.index 0=d) (h2 : s.index 2=r) (hs : Good P s) :
    ∃ t, Block.Eval (Good P) copyBody s 4 t ∧ t.data=s.data ∧ t.index 0=d+1 ∧
      t.index 2=r+1 ∧ t.index d=s.index r ∧
      ∀ i, i≠0 → i≠1 → i≠2 → i≠d → t.index i=s.index i := by
  let a := s.putIndex 1 (s.index (s.index 2))
  let b := a.putIndex (a.index 0) (a.index 1)
  let c := b.putIndex 2 (b.index 2+1)
  let t := c.putIndex 0 (c.index 0+1)
  have ea : Block.Eval (Good P) (.op (.addrLoad 1 2)) s 1 a := Block.Eval.op_addrLoad _ _ _ hs hs
  have eb : Block.Eval (Good P) (.op (.addrStore 0 1)) a 1 b := Block.Eval.op_addrStore _ _ _ hs hs
  have ec : Block.Eval (Good P) (.op (.incr 2 2)) b 1 c := Block.Eval.op_incr _ _ _ hs hs
  have et : Block.Eval (Good P) (.op (.incr 0 0)) c 1 t := Block.Eval.op_incr _ _ _ hs hs
  refine ⟨t,ea.seq (eb.seq (ec.seq et)),rfl,?_,?_,?_,?_⟩
  · simp (disch := omega) [t,c,b,a,h0]
  · simp (disch := omega) [t,c,b,a,h0,h2]
  · simp (disch := omega) [t,c,b,a,h0,h2]
  · intro i i0 i1 i2 id; simp [t,c,b,a,h0,i0,i1,i2,id]

/-- One address-bank copy step, with a frame for every other location. -/
theorem copyBody_spec (P : K → Prop) (s : Memory K) (d r : ℕ) (hd : 4≤d)
    (h0 : s.index 0=d) (h2 : s.index 2=r) (hs : Good P s) :
    ∃ t, Block.Eval (Good P) copyBody s 4 t ∧ t.data=s.data ∧ t.index 0=d+1 ∧
      t.index 2=r+1 ∧ t.index d=s.index r ∧
      ∀ i, i≠0 → i≠1 → i≠2 → i≠d → t.index i=s.index i :=
  body_spec P s d r hd h0 h2 hs

def copyTail : Block := .loop (.addrLT 2 3) copyBody

theorem copyTail_spec (P : K → Prop) (s : Memory K) (b len : ℕ) (hb : 4≤b) (hsep : len≤b)
    (h0 : s.index 0=b+4) (h2 : s.index 2=4) (h3 : s.index 3=len) (hs : Good P s) :
    ∃ t, Block.Eval (Good P) copyTail s (6*(len-4)+1) t ∧ t.data=s.data ∧ t.index 3=len ∧
      (∀ i < 4, t.index (b+i)=s.index (b+i)) ∧
      ∀ (i : ℕ), 4 ≤ i → i < len → t.index (b+i)=s.index i := by
  let I (j : ℕ) (m : Memory K) := m.data=s.data ∧ m.index 0=b+4+j ∧ m.index 2=4+j ∧
    m.index 3=len ∧ (∀ i < 4, m.index (b+i)=s.index (b+i)) ∧
    (∀ i < j, m.index (b+4+i)=s.index (4+i)) ∧ ∀ (i : ℕ), 4 ≤ i → i < len → m.index i=s.index i
  have base : I 0 s := ⟨rfl,by simpa using h0,by simpa using h2,h3,fun _ _ => rfl,
    by omega,fun _ _ _ => rfl⟩
  have step (j : ℕ) (hj : j<len-4) (m : Memory K) (h : I j m) :
      (Cond.addrLT 2 3).test m=true ∧ ∃ t, Block.Eval (Good P) copyBody m 4 t ∧ I (j+1) t := by
    obtain ⟨hd,hm0,hm2,hm3,hfront,hcopied,hraw⟩ := h
    refine ⟨by simp [Cond.test,hm2,hm3]; omega,?_⟩
    have hm : Good P m := fun i => hd ▸ hs i
    obtain ⟨t,et,td,ht0,ht2,hw,hf⟩ := body_spec P m (b+4+j) (4+j) (by omega) hm0 hm2 hm
    refine ⟨t,et,td.trans hd,by omega,by omega,(hf 3 (by decide) (by decide) (by decide) (by omega)).trans hm3,
      ?_,?_,?_⟩
    · intro i hi
      exact (hf _ (by omega) (by omega) (by omega) (by omega)).trans (hfront i hi)
    · intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hij | rfl
      · exact (hf _ (by omega) (by omega) (by omega) (by omega)).trans (hcopied i hij)
      · exact hw.trans (hraw _ (by omega) (by omega))
    · intro i hi hlo
      exact (hf _ (by omega) (by omega) (by omega) (by omega)).trans (hraw i hi hlo)
  have stop (m : Memory K) (h : I (len-4) m) :
      (Cond.addrLT 2 3).test m=false ∧ Good P m := by
    obtain ⟨hd,_,hm2,hm3,_⟩ := h
    exact ⟨by simp [Cond.test,hm2,hm3]; omega,fun i => hd ▸ hs i⟩
  obtain ⟨t,et,td,_,_,ht3,hfront,hcopied,_⟩ :=
    Block.Eval.loop_invariant_exact I s (len-4) 4 base step stop
  refine ⟨t,by simpa [copyTail,Nat.mul_comm] using et,td,ht3,hfront,?_⟩
  intro i hi hlo
  have h := hcopied (i-4) (by omega)
  convert h using 1 <;> congr 1 <;> omega

end Ingress
end Compression
end LinearProgramming
end Optimization
end OAI
