import OAI.Optimization.LinearProgramming.RAM.NatCast

/-! Padded transfer of one ordered minor selector from the address bank to a scalar table row. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

private def nextWord : Block := .branch (.addrLT 28 42)
  (.seq (.op (.addrLoad 29 27)) (.op (.incr 27 27))) (.op (.addrConst 29 0))

/-- Padded entries are stored as zero. Only the actual external request words advance the
input pointer, so this same routine can fill rows and then columns. -/
def stageArray : Block := .seq (.op (.addrConst 28 0)) (.loop (.addrLT 28 22)
  (.seq nextWord (.seq (natCastBlock 0 6 30 29) (.seq (.op (.store 26 0))
    (.seq (.op (.incr 26 26)) (.op (.incr 28 28)))))))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem nextWord_spec (P : K→Prop) (s : Memory K) (i k : ℕ)
    (hi : s.index 28 = i) (hk : s.index 42 = k) (hs : ∀a,P (s.data a)) :
    ∃ t l, l ≤ 4 ∧ Block.Eval (fun z => ∀a,P (z.data a)) nextWord s l t ∧
      t.index 29 = (if i < k then s.index (s.index 27) else 0) ∧
      t.index 27 = s.index 27+(if i < k then 1 else 0) ∧ t.data = s.data ∧
      ∀a,a ≠ 27 → a ≠ 29 → t.index a = s.index a := by
  by_cases h : i < k
  · let u := s.putIndex 29 (s.index (s.index 27))
    let t := u.putIndex 27 (u.index 27+1)
    have eu : Block.Eval (fun z => ∀a,P (z.data a)) (.op (.addrLoad 29 27)) s 1 u := Block.Eval.op_addrLoad _ _ _ hs hs
    have et : Block.Eval (fun z => ∀a,P (z.data a)) (.op (.incr 27 27)) u 1 t := Block.Eval.op_incr _ _ _ hs hs
    exact ⟨t,4,by decide,.branchTrue (by simp [Cond.test,hi,hk,h]) (eu.seq et),by simp [t,u,h],
      by simp [t,u,h],rfl,fun a h₁ h₂ => by simp [t,u,h₁,h₂]⟩
  · let t := s.putIndex 29 0
    have et : Block.Eval (fun z => ∀a,P (z.data a)) (.op (.addrConst 29 0)) s 1 t := Block.Eval.op_addrConst _ _ _ hs hs
    exact ⟨t,2,by decide,.branchFalse (by simp [Cond.test,hi,hk,h]) et,by simp [t,h],by simp [t,h],
      rfl,fun a _ h₂ => by simp [t,h₂]⟩

/-- The exact data and address frames of an address-to-scalar padded array transfer. -/
structure StagedArray (n k src dst : ℕ) (w : ℕ→ℕ) (s t : Memory K) : Prop where
  writes : ∀ i < n, t.data (dst+i) = (w i:K)
  data : ∀ a,a ≠ 0 → a ≠ 6 → (a < dst ∨ dst+n ≤ a) → t.data a = s.data a
  outPtr : t.index 26 = dst+n
  inPtr : t.index 27 = src+k
  indices : ∀ a,a ≠ 26 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 30 → t.index a = s.index a

private structure StageI (P : K→Prop) (k src dst : ℕ) (w : ℕ→ℕ) (start : Memory K) (i : ℕ) (s : Memory K) : Prop where
  safe : ∀a,P (s.data a)
  outPtr : s.index 26 = dst+i
  inPtr : s.index 27 = src+min i k
  counter : s.index 28 = i
  writes : ∀ j < i, s.data (dst+j) = (w j:K)
  data : ∀a,a ≠ 0 → a ≠ 6 → (a < dst ∨ dst+i ≤ a) → s.data a = start.data a
  indices : ∀ a,a ≠ 26 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 30 → s.index a = start.index a

set_option maxHeartbeats 1000000 in
/-- All scalar arithmetic is charged while writing the `n`-cell padded array. The numerical
coordinate values are at most `n`, and the program copies existing scalars directly. -/
theorem stageArray_spec (P : K→Prop) (s : Memory K) (n k src dst : ℕ) (w : ℕ→ℕ)
    (hk : k ≤ n) (hsrc : 40 ≤ src) (hdst : 7 ≤ dst) (h22 : s.index 22 = n) (h42 : s.index 42 = k)
    (h26 : s.index 26 = dst) (h27 : s.index 27 = src) (words : ∀i < k,s.index (src+i) = w i)
    (padding : ∀ i,k ≤ i → w i = 0) (bounded : ∀i < n,w i ≤ n)
    (hs : ∀a,P (s.data a)) (hone : P 1) (hv : ∀j ≤ n,P (j:K)) :
    ∃t l,l ≤ n*(4*n+13)+2 ∧ Block.Eval (fun z => ∀a,P (z.data a)) stageArray s l t ∧
      StagedArray n k src dst w s t := by
  let safe := fun z : Memory K => ∀a,P (z.data a)
  let a := s.putIndex 28 0
  have ea : Block.Eval safe (.op (.addrConst 28 0)) s 1 a := Block.Eval.op_addrConst _ _ _ hs hs
  let I := StageI P k src dst w s
  have init : I 0 a := ⟨hs,by simpa [a] using h26,by simpa [a] using h27,by simp [a],
    fun j hj => (Nat.not_lt_zero _ hj).elim,fun _ _ _ _ => rfl,fun j _ _ h _ _ => by simp [a,h]⟩
  have step (i : ℕ) (hi : i < n) (b : Memory K) (hb : I i b) :
      (Cond.addrLT 28 22).test b = true ∧ ∃t l,l ≤ 4*n+11 ∧ Block.Eval safe
        (.seq nextWord (.seq (natCastBlock 0 6 30 29) (.seq (.op (.store 26 0))
          (.seq (.op (.incr 26 26)) (.op (.incr 28 28)))))) b l t ∧ I (i+1) t := by
    have b22 := (hb.indices 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22
    have b42 := (hb.indices 42 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h42
    refine ⟨by simpa [Cond.test,hb.counter,b22] using hi,?_⟩
    obtain ⟨c,l,hl,ec,c29,c27,cd,ci⟩ := nextWord_spec P b i k hb.counter b42 hb.safe
    have cw : c.index 29 = w i := by
      rw [c29]
      by_cases hx : i < k
      · simp only [hx,ite_true,hb.inPtr,min_eq_left hx.le]
        exact (hb.indices (src+i) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (words _ hx)
      · simp [hx,padding i (by omega)]
    have cnext : c.index 27 = src+min (i+1) k := by
      rw [c27,hb.inPtr]
      by_cases h : i < k
      · simp [h,min_eq_left h.le,Nat.add_assoc]
        exact Nat.succ_le_of_lt h
      · simp [h,min_eq_right (by omega : k ≤ i),min_eq_right (by omega : k ≤ i+1)]
    obtain ⟨d,ed,d0,_,_,di,dd⟩ := natCastBlock_correct P c 0 6 30 29 (w i) (by decide) (by decide) cw
      ec.safe_end hone (fun j hj => hv j (hj.trans (bounded i hi)))
    have d26 := (di 26 (by decide)).trans ((ci 26 (by decide) (by decide)).trans hb.outPtr)
    have d28 := (di 28 (by decide)).trans ((ci 28 (by decide) (by decide)).trans hb.counter)
    let e := d.putData (d.index 26) (d.data 0)
    let f := e.putIndex 26 (e.index 26+1)
    let t := f.putIndex 28 (f.index 28+1)
    have es : safe e := by
      intro j
      by_cases h : j = d.index 26
      · simpa [e,h] using ed.safe_end 0
      · simpa [e,h] using ed.safe_end j
    have ee : Block.Eval safe (.op (.store 26 0)) d 1 e := Block.Eval.op_store _ _ _ ed.safe_end es
    have ef : Block.Eval safe (.op (.incr 26 26)) e 1 f := Block.Eval.op_incr _ _ _ es es
    have et : Block.Eval safe (.op (.incr 28 28)) f 1 t := Block.Eval.op_incr _ _ _ es es
    refine ⟨t,l+((4*w i+4)+(1+(1+1))),by have := bounded i hi; omega,ec.seq (ed.seq (ee.seq (ef.seq et))),es,?_,?_,?_,?_,?_,?_⟩
    · simp [t,f,e,d26,Nat.add_assoc]
    · simpa [t,f,e] using (di 27 (by decide)).trans cnext
    · simp [t,f,e,d28]
    · intro j hj
      by_cases eq : j = i
      · subst j; simp [t,f,e,d26,d0]
      · have hj' : j < i := by omega
        have keep := dd (dst+j) (by omega) (by omega)
        rw [cd,hb.writes j hj'] at keep
        change (d.putData (d.index 26) (d.data 0)).data (dst+j) = _
        exact (Memory.putData_ne d (show dst+j ≠ d.index 26 by rw [d26]; omega) (d.data 0)).trans keep
    · intro x h0 h6 h
      have keep := dd x h0 h6
      rw [cd,hb.data x h0 h6 (by omega)] at keep
      simpa [t,f,e,d26,show x ≠ dst+i by omega] using keep
    · intro j h26' h27' h28' h29' h30'
      simpa [t,f,e,h26',h28'] using (di j h30').trans ((ci j h27' h29').trans (hb.indices j h26' h27' h28' h29' h30'))
  have stop (t : Memory K) (ht : I n t) : (Cond.addrLT 28 22).test t = false ∧ safe t := by
    exact ⟨by simp [Cond.test,ht.counter,(ht.indices 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22],ht.safe⟩
  obtain ⟨t,l,hl,et,ht⟩ := Block.Eval.loop_invariant I a n (4*n+11) init step stop
  have hl' : l ≤ n*(4*n+13)+1 := by simpa only [Nat.add_assoc] using hl
  refine ⟨t,1+l,by omega,ea.seq et,ht.writes,ht.data,ht.outPtr,?_,ht.indices⟩
  simpa [min_eq_right hk] using ht.inPtr

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
