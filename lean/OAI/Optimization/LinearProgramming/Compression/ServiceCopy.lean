import OAI.Optimization.LinearProgramming.RAM.Loops

/-! Moving the original scalar tape seven places to the right during minor-oracle startup.
The move runs backwards so overlapping source and destination are allowed. Scalar zero is
a temporary register and its original value is saved outside both intervals before copying. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

private def shiftDigit : Block :=
  .seq (.op (.decr 8 8)) (.seq (.op (.decr 9 9))
    (.seq (.op (.load 0 8)) (.op (.store 9 0))))

/-- Input length in address register 11 and length plus seven in register 1. -/
def moveServiceInput : Block :=
  .seq (.op (.store 1 0)) (.seq (.op (.addrCopy 8 11)) (.seq (.op (.addrCopy 9 1))
    (.seq (.op (.addrConst 10 1)) (.seq (.loop (.addrLT 10 8) shiftDigit)
      (.seq (.op (.load 0 1)) (.op (.copy 7 0)))))))

private theorem putGood {K : Type*} (P : K → Prop) (s : Memory K) (j : ℕ) (v : K)
    (h : ∀ i, P (s.data i)) (hv : P v) : ∀ i, P ((s.putData j v).data i) := by
  intro i
  by_cases hi : i=j
  · simpa [Memory.putData,hi] using hv
  · simpa [Memory.putData,hi] using h i

private structure ShiftInvariant {K : Type*} (P : K → Prop) (orig : Memory K) (n k : ℕ)
    (s : Memory K) : Prop where
  safe : ∀ i, P (s.data i)
  source : s.index 8 = n-k
  target : s.index 9 = 7+(n-k)
  one : s.index 10 = 1
  saved : s.data (n+7) = orig.data 0
  pending : ∀ j, 1 ≤ j → j < n-k → s.data j = orig.data j
  done : ∀ j, n-k ≤ j → j < n → s.data (7+j) = orig.data j
  keep : ∀ i, i ≠ 8 → i ≠ 9 → i ≠ 10 → s.index i = orig.index i

theorem moveServiceInput_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (n : ℕ) (hsize : s.index 11 = n)
    (hend : s.index 1 = n+7) (hs : ∀ i, P (s.data i)) :
    ∃ t, Block.Eval (fun m => ∀ i, P (m.data i)) moveServiceInput s (6*(n-1)+7) t ∧
      (∀ j < n, t.data (7+j) = s.data j) ∧
      ∀ i, i ≠ 8 → i ≠ 9 → i ≠ 10 → t.index i = s.index i := by
  let good := fun m : Memory K => ∀ i, P (m.data i)
  let a := s.putData (s.index 1) (s.data 0)
  let b := a.putIndex 8 (a.index 11)
  let c := b.putIndex 9 (b.index 1)
  let d := c.putIndex 10 1
  have ha : good a := putGood P s _ _ hs (hs _)
  have ea : Block.Eval good (.op (.store 1 0)) s 1 a := Block.Eval.op_store _ _ _ hs ha
  have eb : Block.Eval good (.op (.addrCopy 8 11)) a 1 b := Block.Eval.op_addrCopy _ _ _ ha ha
  have ec : Block.Eval good (.op (.addrCopy 9 1)) b 1 c := Block.Eval.op_addrCopy _ _ _ ha ha
  have ed : Block.Eval good (.op (.addrConst 10 1)) c 1 d := Block.Eval.op_addrConst _ _ _ ha ha
  have base : ShiftInvariant P s n 0 d := by
    refine ⟨ha, by simp [d,c,b,a,hsize], by simp [d,c,b,a,hend,Nat.add_comm],
      by simp [d], by simp [d,c,b,a,hend], ?_, ?_, ?_⟩
    · intro j _ hj
      have hne : j ≠ n+7 := by omega
      simp [d,c,b,a,hend,hne]
    · intro j h₁ h₂
      omega
    · intro i h₈ h₉ h₁₀
      simp [d,c,b,a,h₈,h₉,h₁₀]
  have step (k : ℕ) (hk : k < n-1) (m : Memory K) (h : ShiftInvariant P s n k m) :
      (Cond.addrLT 10 8).test m = true ∧
        ∃ t, Block.Eval good shiftDigit m 4 t ∧ ShiftInvariant P s n (k+1) t := by
    refine ⟨by simp [Cond.test,h.one,h.source]; omega, ?_⟩
    let i := n-(k+1)
    have hi : 1 ≤ i := by dsimp [i]; omega
    have hi' : i < n-k := by dsimp [i]; omega
    let a := m.putIndex 8 (m.index 8-1)
    let b := a.putIndex 9 (a.index 9-1)
    let c := b.putData 0 (b.data (b.index 8))
    let t := c.putData (c.index 9) (c.data 0)
    have h8 : b.index 8 = i := by simp [b,a,i,h.source,Nat.sub_sub]
    have h9 : c.index 9 = 7+i := by
      simp only [c,b,a,Memory.putData_index,Memory.putIndex_same,Memory.putIndex_ne _ (by decide : 9 ≠ 8) _]
      rw [h.target]
      dsimp [i]; omega
    have hc : good c := putGood P b _ _ h.safe (h.safe _)
    have ht : good t := putGood P c _ _ hc (hc _)
    have ea : Block.Eval good (.op (.decr 8 8)) m 1 a := Block.Eval.op_decr _ _ _ h.safe h.safe
    have eb : Block.Eval good (.op (.decr 9 9)) a 1 b := Block.Eval.op_decr _ _ _ h.safe h.safe
    have ec : Block.Eval good (.op (.load 0 8)) b 1 c := Block.Eval.op_load _ _ _ h.safe hc
    have ed : Block.Eval good (.op (.store 9 0)) c 1 t := Block.Eval.op_store _ _ _ hc ht
    have result : c.data 0 = s.data i := by
      simp only [c,Memory.putData_same,h8, b, a, Memory.putIndex_data]
      exact h.pending i hi hi'
    have untouched (p : ℕ) (hzero : p ≠ 0) (hpos : p ≠ 7+i) : t.data p = m.data p := by
      change (c.putData (c.index 9) (c.data 0)).data p = _
      rw [Memory.putData_ne _ (show p ≠ c.index 9 by rw [h9]; exact hpos) _]
      change (b.putData 0 (b.data (b.index 8))).data p = _
      rw [Memory.putData_ne _ hzero _]
      rfl
    refine ⟨t, ea.seq (eb.seq (ec.seq ed)), ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact h8
    · exact h9
    · simpa [t,c,b,a] using h.one
    · have hne : n+7 ≠ 7+i := by omega
      exact (untouched _ (by omega) hne).trans h.saved
    · intro j hj hji
      have hji' : j < i := hji
      have hne : j ≠ 7+i := by omega
      have hj0 : j ≠ 0 := by omega
      exact (untouched _ hj0 hne).trans (h.pending j hj (lt_trans hji' hi'))
    · intro j hj hnj
      by_cases hji : j=i
      · subst j
        simpa [t,h9] using result
      · have old : n-k ≤ j := by dsimp [i] at hji; omega
        have hne : 7+j ≠ 7+i := by omega
        exact (untouched _ (by omega) hne).trans (h.done j old hnj)
    · intro p h₈ h₉ h₁₀
      simpa [t,c,b,a,h₈,h₉] using h.keep p h₈ h₉ h₁₀
  have stop (m : Memory K) (h : ShiftInvariant P s n (n-1) m) :
      (Cond.addrLT 10 8).test m = false ∧ good m := by
    refine ⟨?_,h.safe⟩
    simp [Cond.test,h.source,h.one]; omega
  obtain ⟨v, ev, hv⟩ := Block.Eval.loop_invariant_exact (ShiftInvariant P s n) d (n-1) 4 base step stop
  have hv1 := (hv.keep 1 (by decide) (by decide) (by decide)).trans hend
  let w := v.putData 0 (v.data (v.index 1))
  let t := w.putData 7 (w.data 0)
  have hw : good w := putGood P v _ _ hv.safe (hv.safe _)
  have ht : good t := putGood P w _ _ hw (hw _)
  have ew : Block.Eval good (.op (.load 0 1)) v 1 w := Block.Eval.op_load _ _ _ hv.safe hw
  have et : Block.Eval good (.op (.copy 7 0)) w 1 t := Block.Eval.op_copy _ _ _ hw ht
  refine ⟨t, ?_, ?_, hv.keep⟩
  · unfold moveServiceInput
    convert ea.seq (eb.seq (ec.seq (ed.seq (ev.seq (ew.seq et))))) using 1
    omega
  · intro j hj
    by_cases hz : j=0
    · subst j
      simpa [t,w,hv1] using hv.saved
    · have hne : 7+j ≠ 7 := by omega
      change (w.putData 7 (w.data 0)).data (7+j) = _
      rw [Memory.putData_ne _ hne _]
      change (v.putData 0 (v.data (v.index 1))).data (7+j) = _
      rw [Memory.putData_ne _ (by omega : 7+j ≠ 0) _]
      exact hv.done j (by omega) hj

end Compression
end LinearProgramming
end Optimization
end OAI
