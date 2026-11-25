import OAI.Optimization.LinearProgramming.Compression.SmallProxyPack
import OAI.Optimization.LinearProgramming.Compression.ProxyPrepared

/-! Materialize both arguments and all four flat-input metadata cells for a
framed invocation of the numerical proxy evaluator. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

private def scalarTapeLengthBlock : Block :=
  .seq (.op (.addrConst 56 5)) (.forRange 4 0 (.seq (.op (.incr 56 56)) (.op (.incr 56 56))))

private theorem scalarTapeLength_spec {P : ℚ → Prop} (m : Memory ℚ) (n : ℕ)
    (hm : m.AllData P) (hn : m.index 0=n) :
    ∃ t, Block.Eval (Memory.AllData P) scalarTapeLengthBlock m (5*n+3) t ∧
      t.data=m.data ∧ t.index 56=2*n+5 ∧ ∀ i, i≠4 → i≠56 → t.index i=m.index i := by
  let a := m.putIndex 56 5
  let I := fun j (z : Memory ℚ) => z.data=m.data ∧ z.index 4=j ∧ z.index 56=5+2*j ∧
    ∀ i, i≠4 → i≠56 → z.index i=m.index i
  have start : I 0 (a.putIndex 4 0) := by
    refine ⟨rfl, by simp, by simp [a], ?_⟩
    intro i h4 h56
    simp [a,h4,h56]
  obtain ⟨t, run, hd, _, hv, hf⟩ := Block.Eval.forRange_invariant_exact
    (safe := Memory.AllData P) (body := .seq (.op (.incr 56 56)) (.op (.incr 56 56)))
    4 0 n 2 I a hm start (fun _ s hs =>
      ⟨fun i => by simpa only [hs.1] using hm i, hs.2.1,
        (hs.2.2.2 0 (by decide) (by decide)).trans hn⟩) (by
      intro j _ s hs
      obtain ⟨hdata,hcount,hsize,hframe⟩ := hs
      have ss : s.AllData P := fun i => by simpa only [hdata] using hm i
      let u := s.putIndex 56 (s.index 56+1)
      let v := u.putIndex 56 (u.index 56+1)
      have e₁ : Block.Eval (Memory.AllData P) (.op (.incr 56 56)) s 1 u :=
        Block.Eval.op_incr _ _ _ ss ss
      have e₂ : Block.Eval (Memory.AllData P) (.op (.incr 56 56)) u 1 v :=
        Block.Eval.op_incr _ _ _ e₁.safe_end e₁.safe_end
      refine ⟨v, e₁.seq e₂, hdata, by simp [v,u,hcount], ?_, ?_⟩
      · simp [v,u,hsize,Nat.mul_succ,Nat.add_assoc]
      · intro i h4 h56
        simpa [v,u,h4,h56] using hframe i h4 h56)
  refine ⟨t, ?_, hd, hv.trans (Nat.add_comm ..), hf⟩
  rw [show 5*n+3 = 1+(n*(2+3)+2) by omega]
  exact (Block.Eval.op_addrConst m 56 5 hm hm).seq run

private def smallProxyCallHeader : Block :=
  .seq scalarTapeLengthBlock <| .seq (.op (.addrCopy 55 3)) <| .seq (.op (.addrCopy 57 9)) <|
    .seq (.op (.addrConst 58 1)) <| .seq (.op (.incr 4 0)) (.op (.addrStore 9 4))

private theorem smallProxyCallHeader_spec {P : ℚ → Prop} (m : Memory ℚ) (n : ℕ)
    (hm : m.AllData P) (hn : m.index 0=n) (hslot : 59 ≤ m.index 9) :
    ∃ z, Block.Eval (Memory.AllData P) smallProxyCallHeader m (5*n+8) z ∧
      z.data=m.data ∧ z.index 55=m.index 3 ∧ z.index 56=2*n+5 ∧ z.index 57=m.index 9 ∧
      z.index 58=1 ∧ z.index (m.index 9)=n+1 ∧
      ∀ i, i≠4 → i≠55 → i≠56 → i≠57 → i≠58 → i≠m.index 9 → z.index i=m.index i := by
  obtain ⟨t, lengthEval, hdata, hlen, frame⟩ := scalarTapeLength_spec m n hm hn
  let a := t.putIndex 55 (t.index 3)
  let b := a.putIndex 57 (a.index 9)
  let c := b.putIndex 58 1
  let d := c.putIndex 4 (c.index 0+1)
  let z := d.putIndex (d.index 9) (d.index 4)
  have e₁ : Block.Eval (Memory.AllData P) (.op (.addrCopy 55 3)) t 1 a :=
    Block.Eval.op_addrCopy _ _ _ lengthEval.safe_end lengthEval.safe_end
  have e₂ : Block.Eval (Memory.AllData P) (.op (.addrCopy 57 9)) a 1 b :=
    Block.Eval.op_addrCopy _ _ _ e₁.safe_end e₁.safe_end
  have e₃ : Block.Eval (Memory.AllData P) (.op (.addrConst 58 1)) b 1 c :=
    Block.Eval.op_addrConst _ _ _ e₂.safe_end e₂.safe_end
  have e₄ : Block.Eval (Memory.AllData P) (.op (.incr 4 0)) c 1 d :=
    Block.Eval.op_incr _ _ _ e₃.safe_end e₃.safe_end
  have e₅ : Block.Eval (Memory.AllData P) (.op (.addrStore 9 4)) d 1 z :=
    Block.Eval.op_addrStore _ _ _ e₄.safe_end e₄.safe_end
  have t0 := (frame 0 (by decide) (by decide)).trans hn
  have t3 := frame 3 (by decide) (by decide)
  have t9 := frame 9 (by decide) (by decide)
  have d9 : d.index 9=m.index 9 := by simp [d,c,b,a,t9]
  have d4 : d.index 4=n+1 := by simp [d,c,b,a,t0]
  have keep (i : ℕ) (hne : i≠m.index 9) : z.index i=d.index i := Memory.putIndex_ne _ (d9 ▸ hne) _
  refine ⟨z, ?_, hdata, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 5*n+8=(5*n+3)+(1+(1+(1+(1+1)))) by omega]
    exact lengthEval.seq (e₁.seq (e₂.seq (e₃.seq (e₄.seq e₅))))
  · rw [keep 55 (by omega)]; simp [d,c,b,a,t3]
  · rw [keep 56 (by omega)]; simp [d,c,b,a,hlen]
  · rw [keep 57 (by omega)]; simp [d,c,b,a,t9]
  · rw [keep 58 (by omega)]; simp [d,c]
  · rw [← d9]
    exact (Memory.putIndex_same ..).trans d4
  · intro i h4 h55 h56 h57 h58 hs
    rw [keep i hs]
    simpa [d,c,b,a,h4,h55,h57,h58] using frame i h4 h56

/-- The flat scalar input is staged at address register 3. The singleton
dimension array is staged at the address held in register 9; the caller
metadata cells 55–58 identify both streams. -/
def framedSmallProxyPackBlock : Block := .seq smallProxyPackBlock smallProxyCallHeader

theorem framedSmallProxyPackBlock_spec {P : ℚ → Prop} (m : Memory ℚ) (n D : ℕ) (c : ℤ)
    (a grid : Fin n → ℤ) (hm : m.AllData P) (h0 : P 0) (hn : m.index 0=n)
    (hD : m.data 8=(D:ℚ)) (hR : 0<m.index 1) (hG : 0<m.index 2) (hO : 8<m.index 3)
    (hslot : 59 ≤ m.index 9)
    (hRsep : m.index 1+n<m.index 3 ∨ m.index 3+2*n+5 ≤ m.index 1)
    (hGsep : m.index 2+n ≤ m.index 3 ∨ m.index 3+2*n+5 ≤ m.index 2)
    (ha : ∀ i : Fin n, m.data (m.index 1+i)=(a i:ℚ))
    (hc : m.data (m.index 1+n)=(c:ℚ)) (hg : ∀ i : Fin n, m.data (m.index 2+i)=(grid i:ℚ)) :
    ∃ z, Block.Eval (Memory.AllData P) framedSmallProxyPackBlock m (21*n+51) z ∧
      (∀ j<(smallProxyScalarTape D c a grid).length,
        z.data (m.index 3+j)=(smallProxyScalarTape D c a grid)[j]?.getD 0) ∧
      z.index 55=m.index 3 ∧ z.index 56=(smallProxyScalarTape D c a grid).length ∧
      z.index 57=m.index 9 ∧ z.index 58=1 ∧ z.index (m.index 9)=n+1 ∧
      (∀ i, i≠0 → (i<m.index 3 ∨ m.index 3+2*n+5 ≤ i) → z.data i=m.data i) ∧
      (∀ i, (i < 4 ∨ 8 < i) → i≠55 → i≠56 → i≠57 → i≠58 → i≠m.index 9 → z.index i=m.index i) := by
  obtain ⟨u, pack, words, sf, ai⟩ :=
    smallProxyPackBlock_spec m n D c a grid hm h0 hn hD hR hG hO hRsep hGsep ha hc hg
  have u0 := ai 0 (Or.inl (by decide))
  have u3 := ai 3 (Or.inl (by decide))
  have u9 := ai 9 (Or.inr (by decide))
  obtain ⟨z, head, data, base, len, slot, one, dim, fi⟩ :=
    smallProxyCallHeader_spec u n pack.safe_end (u0.trans hn) (u9 ▸ hslot)
  refine ⟨z, ?_, ?_, base.trans u3, ?_, slot.trans u9, one, ?_, ?_, ?_⟩
  · rw [show 21*n+51=(16*n+43)+(5*n+8) by omega]
    exact pack.seq head
  · simpa only [data] using words
  · simpa only [smallProxyScalarTape_length] using len
  · simpa only [u9] using dim
  · simpa only [data] using sf
  · intro i hi h55 h56 h57 h58 h9
    exact (fi i (by omega) h55 h56 h57 h58 (u9 ▸ h9)).trans (ai i hi)

/-- The staged protocol is exactly the small branch of the prepared query object. -/
theorem preparedProxyQuery_small_input {n : ℕ} (fuel prec : ℕ) (c : ℤ) (a : Fin n → ℤ)
    (mag : Fin n → ℚ) (h : proxyLargeIndices fuel prec mag=[]) :
    preparedProxyQuery fuel prec c a mag =
      ⟨false, [n+1], smallProxyScalarTape (2^(prec+2)) c a
        (fun i => (logProxyNumerator fuel prec (mag i)).getD 0)⟩ := by
  simp [preparedProxyQuery,h,smallProxyScalarTape]

end Compression
end LinearProgramming
end Optimization
end OAI
