import OAI.Optimization.LinearProgramming.Compression.PowerTapeEncoder
import OAI.Optimization.LinearProgramming.RAM.Array

/-! A fixed RAM transducer scans a scalar digit page backwards and appends its
most-significant-first power tokens to an address page. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
open RAM

private def copyDigit : Block :=
  .seq (.straight [.decr 2 2, .load 40 2])
    (.seq (.branch (.scalarLT 40 41) (.op (.addrConst 39 1)) (.op (.addrConst 39 2)))
      (.straight [.addrStore 34 39, .incr 34 34]))

/-- Address register 2 is one past the last little-endian input digit, register
0 holds the digit count, and register 34 points to the next free token. -/
def copyPowerDigitsBlock : Block :=
  .seq (.op (.const 41 1)) (.forRange 42 0 copyDigit)

private theorem copyDigit_run (m : Memory ℚ) {P : ℚ → Prop} (hm : m.AllData P)
    (b : Bool) (hb : m.data (m.index 2-1) = (b.toNat : ℚ))
    (hone : m.data 41 = 1) (hout : 42 < m.index 34) :
    ∃ t k, k ≤ 7 ∧ Block.Eval (Memory.AllData P) copyDigit m k t ∧
      t.index 2 = m.index 2-1 ∧ t.index 34=m.index 34+1 ∧
      t.index (m.index 34) = (PowerToken.bit b).code ∧
      (∀ i, i ≠ 2 → i ≠ 34 → i ≠ 39 → i ≠ m.index 34 → t.index i=m.index i) ∧
      (∀ i, i ≠ 40 → t.data i = m.data i) := by
  let s₁ := m.putIndex 2 (m.index 2-1)
  let s₂ := s₁.putData 40 (s₁.data (s₁.index 2))
  let s₃ := s₂.putIndex 39 (PowerToken.bit b).code
  let s₄ := s₃.putIndex (s₃.index 34) (s₃.index 39)
  let t := s₄.putIndex 34 (s₄.index 34+1)
  have h₁ : s₁.AllData P := hm
  have h₂ : s₂.AllData P := h₁.putData _ (h₁ _)
  have h₃ : s₃.AllData P := h₂
  have h₄ : s₄.AllData P := h₃
  have ht : t.AllData P := h₄
  have e₁ := Block.Eval.op_decr m 2 2 hm h₁
  have e₂ := Block.Eval.op_load s₁ 40 2 h₁ h₂
  have e₄ := Block.Eval.op_addrStore s₃ 34 39 h₃ h₄
  have e₅ := Block.Eval.op_incr s₄ 34 34 h₄ ht
  have e₃ : ∃ k ≤ 3, Block.Eval (Memory.AllData P)
      (.branch (.scalarLT 40 41) (.op (.addrConst 39 1)) (.op (.addrConst 39 2))) s₂ k s₃ := by
    cases b with
    | false =>
      have hc : (Cond.scalarLT 40 41).test s₂ = true := by simp [Cond.test,s₂,s₁,hb,hone]
      exact ⟨3,le_rfl,Block.Eval.branchTrue (k:=1) hc (Block.Eval.op_addrConst s₂ 39 1 h₂ h₃)⟩
    | true =>
      have hc : (Cond.scalarLT 40 41).test s₂ = false := by simp [Cond.test,s₂,s₁,hb,hone]
      exact ⟨2,by decide,Block.Eval.branchFalse (k:=1) hc (Block.Eval.op_addrConst s₂ 39 2 h₂ h₃)⟩
  obtain ⟨j,hj,ej⟩ := e₃
  refine ⟨t,2+(j+2),by omega,(e₁.seq (e₂.seq (.skip h₂))).seq (ej.seq (e₄.seq (e₅.seq (.skip ht)))),
    ?_,?_,?_,?_,?_⟩
  · simp [t,s₄,s₃,s₂,s₁,show 2 ≠ m.index 34 by omega]
  · simp [t,s₄,s₃,s₂,s₁,show 34 ≠ m.index 34 by omega]
  · simp [t,s₄,s₃,s₂,s₁,show m.index 34 ≠ 34 by omega]
  · intro i h2 h34 h39 ho; simp [t,s₄,s₃,s₂,s₁,h2,h34,h39,ho]
  · intro i h40; simp [t,s₄,s₃,s₂,s₁,h40]

private structure CopyState {k : ℕ} (bs : Fin k → Bool) (orig : Memory ℚ)
    (P : ℚ → Prop) (base out j : ℕ) (s : Memory ℚ) : Prop where
  safe : s.AllData P
  count : s.index 42 = j
  size : s.index 0 = k
  source : s.index 2 = base+k-j
  target : s.index 34 = out+j
  one : s.data 41=1
  dataFrame : ∀ i, i ≠ 40 → i ≠ 41 → s.data i=orig.data i
  codes : ∀ i : Fin k, i.val < j → s.index (out+i.val) = (PowerToken.bit (bs i)).code
  indexFrame : ∀ i, i ≠ 2 → i ≠ 34 → i ≠ 39 → i ≠ 42 →
    (i < out ∨ out+j ≤ i) → s.index i=orig.index i

/-- Exact output code at every digit, full framing outside the destination and
a linear number of scalar and indirect-address operations. The output interval
may already contain arbitrary values. -/
theorem copyPowerDigitsBlock_spec {k : ℕ} (bs : Fin k → Bool) (m : Memory ℚ)
    (base out : ℕ) {P : ℚ → Prop} (hm : m.AllData P) (hp : P 1)
    (hk : m.index 0=k) (hb : m.index 2=base+k) (ho : m.index 34=out)
    (hbase : 41 < base) (hout : 42 < out)
    (hbits : ∀ i : Fin k, m.data (base+(k-1-i.val)) = ((bs i).toNat : ℚ)) :
    ∃ s time, time ≤ 10*k+3 ∧ Block.Eval (Memory.AllData P) copyPowerDigitsBlock m time s ∧
      s.index 2=base ∧ s.index 34=out+k ∧ (∀ i : Fin k, s.index (out+i.val) = (PowerToken.bit (bs i)).code) ∧
      (∀ i, i ≠ 40 → i ≠ 41 → s.data i=m.data i) ∧
      (∀ i, i ≠ 2 → i ≠ 34 → i ≠ 39 → i ≠ 42 → (i < out ∨ out+k ≤ i) →
        s.index i=m.index i) := by
  let u := m.putData 41 1
  have hu : u.AllData P := hm.putData _ hp
  have head := Block.Eval.op_const m 41 1 hm hu
  have begin : CopyState bs m P base out 0 (u.putIndex 42 0) := by
    refine ⟨hu,by simp,by simpa [u] using hk,by simpa [u] using hb,by simpa [u] using ho,
      by simp [u],?_,by simp,?_⟩
    · intro i _ h41; simp [u,h41]
    · intro i _ _ _ h42 _; simp [u,h42]
  have run := Block.Eval.forRange_invariant (safe:=Memory.AllData P) (body:=copyDigit)
    42 0 k 7 (CopyState bs m P base out) u hu begin
    (fun _ _ h => ⟨h.safe,h.count,h.size⟩) (by
      intro j hj s hs
      let q : Fin k := ⟨j,hj⟩
      have hsrc : s.index 2 - 1 = base+(k-1-j) := by rw [hs.source]; omega
      have hd : s.data (s.index 2-1) = ((bs q).toNat : ℚ) := by
        rw [hsrc,hs.dataFrame _ (by omega) (by omega)]
        exact hbits q
      obtain ⟨t,cost,hcost,ec,hsource,htarget,written,ifr,dfr⟩ :=
        copyDigit_run s hs.safe (bs q) hd hs.one (by rw [hs.target];omega)
      let z := t.putIndex 42 (t.index 42+1)
      have hti (i : ℕ) (h₂ : i ≠ 2) (h34 : i ≠ 34) (h39 : i ≠ 39)
          (hptr : i ≠ out+j) : t.index i=s.index i := ifr i h₂ h34 h39 (hs.target ▸ hptr)
      have hzidx (i : ℕ) (h42 : i ≠ 42) : z.index i=t.index i := by simp [z,h42]
      refine ⟨t,cost,hcost,ec,?_⟩
      change CopyState bs m P base out (j+1) z
      refine ⟨ec.safe_end,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · simp [z,hti 42 (by decide) (by decide) (by decide) (by omega),hs.count]
      · exact (hzidx _ (by decide)).trans ((hti 0 (by decide) (by decide) (by decide) (by omega)).trans hs.size)
      · rw [hzidx _ (by decide),hsource,hs.source]; omega
      · rw [hzidx _ (by decide),htarget,hs.target];omega
      · exact (dfr 41 (by decide)).trans hs.one
      · intro i h40 h41; exact (dfr _ h40).trans (hs.dataFrame _ h40 h41)
      · intro i hi
        rw [hzidx _ (by omega)]
        by_cases hh : i.val = j
        · have he : i=q := Fin.ext hh
          simpa [he,q,hs.target] using written
        · exact (hti _ (by omega) (by omega) (by omega) (by omega)).trans (hs.codes i (by omega))
      · intro i h₂ h34 h39 h42 hr
        exact (hzidx _ h42).trans ((hti _ h₂ h34 h39 (by omega)).trans
          (hs.indexFrame _ h₂ h34 h39 h42 (by omega))))
  obtain ⟨s,cost,hcost,ec,hs⟩ := run
  exact ⟨s,1+cost,by omega,head.seq ec,by rw [hs.source];omega,hs.target,fun i => hs.codes i i.isLt,hs.dataFrame,hs.indexFrame⟩

end Compression
end LinearProgramming
end Optimization
end OAI
