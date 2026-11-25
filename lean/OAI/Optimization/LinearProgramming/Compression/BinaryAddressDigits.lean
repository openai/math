import OAI.Optimization.LinearProgramming.RAM.Array
import Mathlib.Tactic

/-! # Publishing a scalar bit word into the address-register bank

The address output starts at or beyond register 3. The only fixed address
registers used by the code are 0, 1 and 2, so long output words cannot
overwrite a loop counter, bound, or cursor. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

private def chooseAddressBit : Block :=
  .branch (.scalarLT 4 8) (.op (.addrConst 0 1)) (.op (.addrConst 0 0))

private def writeAddressDigit : Block :=
  .seq (.op (.load 8 1)) <| .seq chooseAddressBit <| .seq (.op (.addrStore 2 0)) <|
    .seq (.op (.incr 1 1)) <| .seq (.op (.incr 2 2)) (.op (.sub 3 3 5))

/-- Data register 3 gives the constructed length. Address registers 1 and 2
give the current scalar source and the address destination. -/
def addressDigitsBlock : Block :=
  .seq (.op (.const 4 0)) <| .seq (.op (.const 5 1)) <|
    .loop (.scalarLT 4 3) writeAddressDigit

private theorem writeAddressDigit_spec {P : ℚ → Prop} (m : Memory ℚ) (digit rem : ℕ)
    (hm : m.AllData P) (hbit : digit ≤ 1) (hsource : m.data (m.index 1) = (digit : ℚ))
    (hr : m.data 3 = (rem+1 : ℕ)) (hzero : m.data 4=0) (hone : m.data 5=1)
    (hout : 3 ≤ m.index 2) (hsafe : P (rem : ℚ)) :
    ∃ z, Block.Eval (Memory.AllData P) writeAddressDigit m (7+digit) z ∧
      z.data 3=(rem:ℚ) ∧ (∀ i, i ≠ 3 → i ≠ 8 → z.data i=m.data i) ∧
      z.index 1=m.index 1+1 ∧ z.index 2=m.index 2+1 ∧ z.index (m.index 2)=digit ∧
      (∀ i, 3 ≤ i → i ≠ m.index 2 → z.index i = m.index i) := by
  let u := m.putData 8 (m.data (m.index 1))
  let v := u.putIndex 0 digit
  let w := v.putIndex (v.index 2) (v.index 0)
  let s := w.putIndex 1 (w.index 1+1)
  let t := s.putIndex 2 (s.index 2+1)
  let z := t.putData 3 (t.data 3-t.data 5)
  have load : Block.Eval (Memory.AllData P) (.op (.load 8 1)) m 1 u :=
    Block.Eval.op_load _ _ _ hm (hm.putData _ (hm _))
  have choose : Block.Eval (Memory.AllData P) chooseAddressBit u (2+digit) v := by
    obtain rfl | rfl : digit=0 ∨ digit=1 := by omega
    · exact .branchFalse (by simp [Cond.test,u,hsource,hzero])
        (Block.Eval.op_addrConst u 0 0 load.safe_end load.safe_end)
    · exact .branchTrue (by simp [Cond.test,u,hsource,hzero])
        (Block.Eval.op_addrConst u 0 1 load.safe_end load.safe_end)
  have emit : Block.Eval (Memory.AllData P) (.op (.addrStore 2 0)) v 1 w :=
    Block.Eval.op_addrStore _ _ _ choose.safe_end choose.safe_end
  have incrS : Block.Eval (Memory.AllData P) (.op (.incr 1 1)) w 1 s :=
    Block.Eval.op_incr _ _ _ emit.safe_end emit.safe_end
  have incrD : Block.Eval (Memory.AllData P) (.op (.incr 2 2)) s 1 t :=
    Block.Eval.op_incr _ _ _ incrS.safe_end incrS.safe_end
  have hsub : t.data 3-t.data 5=(rem:ℚ) := by simp [t,s,w,v,u,hr,hone]
  have sub : Block.Eval (Memory.AllData P) (.op (.sub 3 3 5)) t 1 z :=
    Block.Eval.op_sub _ _ _ _ incrD.safe_end (incrD.safe_end.putData _ (hsub ▸ hsafe))
  have v2 : v.index 2=m.index 2 := by simp [v,u]
  have v0 : v.index 0=digit := by simp [v]
  have w1 : w.index 1=m.index 1 := by simp [w,v,u,show 1 ≠ m.index 2 by omega]
  have w2 : w.index 2=m.index 2 := by simp [w,v,u,show 2 ≠ m.index 2 by omega]
  have s2 : s.index 2=m.index 2 := by simp [s,w2]
  refine ⟨z, ?_, (Memory.putData_same ..).trans hsub, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 7+digit=1+((2+digit)+(1+(1+(1+1)))) by omega]
    exact load.seq (choose.seq (emit.seq (incrS.seq (incrD.seq sub))))
  · intro i h3 h8
    exact (Memory.putData_ne t h3 _).trans (Memory.putData_ne m h8 _)
  · simp [z,t,s,w1]
  · simp [z,t,s2]
  · have hold : t.index (m.index 2)=w.index (m.index 2) :=
      (Memory.putIndex_ne s (show m.index 2 ≠ 2 by omega) _).trans
        (Memory.putIndex_ne w (show m.index 2 ≠ 1 by omega) _)
    change t.index (m.index 2)=digit
    rw [hold, ← v2, show w.index (v.index 2)=v.index 0 from Memory.putIndex_same .., v0]
  · intro i hi hne
    exact (Memory.putIndex_ne s (show i ≠ 2 by omega) _).trans <|
      (Memory.putIndex_ne w (show i ≠ 1 by omega) _).trans <|
      (Memory.putIndex_ne v (v2 ▸ hne) _).trans (Memory.putIndex_ne u (show i ≠ 0 by omega) _)

private structure AddressDigitInv (P : ℚ → Prop) (m : Memory ℚ) (digit : ℕ → ℕ)
    (n j : ℕ) (s : Memory ℚ) : Prop where
  safe : s.AllData P
  remaining : s.data 3=((n-j : ℕ):ℚ)
  zero : s.data 4=0
  one : s.data 5=1
  source : s.index 1=m.index 1+j
  destination : s.index 2=m.index 2+j
  dataFrame (i : ℕ) : i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 8 → s.data i=m.data i
  written (i : ℕ) : i < j → s.index (m.index 2+i)=digit i
  indexFrame (i : ℕ) : 3 ≤ i → (i < m.index 2 ∨ m.index 2+j ≤ i) → s.index i=m.index i

/-- The loop includes two controls per digit, the true branch's additional
jump for each one, and one final failed guard. -/
def addressDigitLoopSteps (digit : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k+1, j => 1+(7+digit j)+1+addressDigitLoopSteps digit k (j+1)

private theorem addressDigitLoopSteps_formula (digit : ℕ → ℕ) (k j : ℕ) :
    addressDigitLoopSteps digit k j=9*k+(∑ i ∈ Finset.range k, digit (j+i))+1 := by
  induction k generalizing j with
  | zero => simp [addressDigitLoopSteps]
  | succ k ih =>
    rw [addressDigitLoopSteps, ih, Finset.sum_range_succ']
    simp only [Nat.add_zero]
    have eqSum : (∑ i ∈ Finset.range k, digit (j+(i+1))) =
        ∑ i ∈ Finset.range k, digit (j+1+i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg digit (by omega)
    rw [eqSum]
    omega

/-- Publish n scalar bits in order into the native address bank. On return both
address cursors point just after their words. Only address registers 0–2 and
the destination window, and scalar registers 3,4,5,8, are written. The scalar
source can be anywhere disjoint from those four scratch cells. -/
theorem addressDigitsBlock_spec {P : ℚ → Prop} (m : Memory ℚ) (n : ℕ) (digit : ℕ → ℕ)
    (hm : m.AllData P) (hn : m.data 3=(n:ℚ)) (hout : 3 ≤ m.index 2)
    (hbit : ∀ i < n, digit i ≤ 1) (hinput : ∀ i < n, m.data (m.index 1+i)=(digit i:ℚ))
    (hsrc : ∀ i < n, m.index 1+i ≠ 3 ∧ m.index 1+i ≠ 4 ∧ m.index 1+i ≠ 5 ∧ m.index 1+i ≠ 8)
    (hP : ∀ i : ℕ, i ≤ max n 1 → P (i:ℚ)) :
    ∃ z, Block.Eval (Memory.AllData P) addressDigitsBlock m
        (9*n+(∑ i ∈ Finset.range n, digit i)+3) z ∧
      z.data 3=0 ∧ z.index 1=m.index 1+n ∧ z.index 2=m.index 2+n ∧
      (∀ i < n, z.index (m.index 2+i)=digit i) ∧
      (∀ i, i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 8 → z.data i=m.data i) ∧
      (∀ i, 3 ≤ i → (i < m.index 2 ∨ m.index 2+n ≤ i) → z.index i=m.index i) := by
  let u := m.putData 4 0
  let v := u.putData 5 1
  have ez : Block.Eval (Memory.AllData P) (.op (.const 4 0)) m 1 u :=
    Block.Eval.op_const m 4 0 hm (hm.putData _ (by simpa using hP 0 (Nat.zero_le _)))
  have eo : Block.Eval (Memory.AllData P) (.op (.const 5 1)) u 1 v :=
    Block.Eval.op_const u 5 1 ez.safe_end
      (ez.safe_end.putData _ (by simpa using hP 1 (Nat.le_max_right ..)))
  have start : AddressDigitInv P m digit n 0 v := by
    refine ⟨eo.safe_end, by simp [v,u,hn], by simp [v,u], by simp [v], by simp [v,u],
      by simp [v,u], ?_, fun i hi => by omega, fun _ _ _ => rfl⟩
    intro i _ h4 h5 _
    exact (Memory.putData_ne u h5 _).trans (Memory.putData_ne m h4 _)
  have loop (r j : ℕ) (s : Memory ℚ) (hj : j+r=n) (hs : AddressDigitInv P m digit n j s) :
      ∃ z, Block.Eval (Memory.AllData P) (.loop (.scalarLT 4 3) writeAddressDigit) s
          (addressDigitLoopSteps digit r j) z ∧ AddressDigitInv P m digit n n z := by
    induction r generalizing j s with
    | zero =>
      have h : j=n := by omega
      subst j
      exact ⟨s, .loopFalse (by simp [Cond.test,hs.zero,hs.remaining]) hs.safe, hs⟩
    | succ r ih =>
      have hlt : j < n := by omega
      have hrem : n-j=r+1 := by omega
      have hr : s.data 3=(r+1 : ℕ) := hs.remaining.trans (by rw [hrem])
      have test : (Cond.scalarLT 4 3).test s=true := by
        simp only [Cond.test,hs.zero,hr,decide_eq_true_eq]
        positivity
      obtain ⟨h3,h4,h5,h8⟩ := hsrc j hlt
      have read : s.data (s.index 1)=(digit j:ℚ) := by
        rw [hs.source]
        exact (hs.dataFrame _ h3 h4 h5 h8).trans (hinput j hlt)
      obtain ⟨w, ew, remain, df, p1, p2, cell, idx⟩ := writeAddressDigit_spec s (digit j) r
        hs.safe (hbit j hlt) read hr hs.zero hs.one (by rw [hs.destination]; omega)
        (hP r (by omega))
      have next : AddressDigitInv P m digit n (j+1) w := by
        refine ⟨ew.safe_end, ?_, (df 4 (by decide) (by decide)).trans hs.zero,
          (df 5 (by decide) (by decide)).trans hs.one, ?_, ?_, ?_, ?_, ?_⟩
        · rw [remain, show n-(j+1)=r by omega]
        · simp only [p1,hs.source,Nat.add_assoc]
        · simp only [p2,hs.destination,Nat.add_assoc]
        · intro i hi3 hi4 hi5 hi8
          exact (df i hi3 hi8).trans (hs.dataFrame i hi3 hi4 hi5 hi8)
        · intro i hi
          by_cases e : i=j
          · subst i
            simpa only [hs.destination] using cell
          · have ne : m.index 2+i ≠ s.index 2 := by rw [hs.destination]; omega
            exact (idx _ (by omega) ne).trans (hs.written i (by omega))
        · intro i hi hw
          have ne : i ≠ s.index 2 := by rw [hs.destination]; omega
          exact (idx _ hi ne).trans (hs.indexFrame i hi (by omega))
      obtain ⟨z, el, hz⟩ := ih (j+1) w (by omega) next
      exact ⟨z, .loopTrue test ew el, hz⟩
  obtain ⟨z,run,fin⟩ := loop n 0 v (by omega) start
  refine ⟨z, ?_, by simpa using fin.remaining, fin.source, fin.destination, fin.written, fin.dataFrame,
    fin.indexFrame⟩
  have total := ez.seq (eo.seq run)
  rw [addressDigitLoopSteps_formula] at total
  simp only [Nat.zero_add] at total
  convert total using 1 <;> first | rfl | omega

end Compression
end LinearProgramming
end Optimization
end OAI
