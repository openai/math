import Mathlib.Tactic.IntervalCases
import OAI.Optimization.LinearProgramming.Compression.IngressPrefix
import OAI.Optimization.LinearProgramming.Compression.IngressPointers
import OAI.Optimization.LinearProgramming.Compression.IngressTail
import OAI.Optimization.LinearProgramming.OracleSpec.Compression

/-! The fixed request-ingress program. It accepts the sealed variable-length address
prefix verbatim and copies it above the scratch region without destroying unread words. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Ingress

open RAM

def stageRequest : Block :=
  .seq saveTag (.seq consumeOrder (.seq prepareFreshAddress (.seq shieldPrefix
    (.seq prepareEnd (.seq copyTail exposeBuffer)))))

def stageCost (k : ℕ) := 8 + ((4*k+1) + ((6*k+2) + (13 + (70 + ((6*(2+2*k-4)+1)+71)))))

theorem stageCost_le (k : ℕ) : stageCost k ≤ 22*k+166 := by unfold stageCost; omega

/-- The live request address bank. All positions are numerical addresses obtained by
executing the program. No bound is assumed on any word after the incoming prefix. -/
structure Buffered {K : Type*} (tag k : ℕ) (words : ℕ → ℕ) (t : Memory K) : Prop where
  base : t.index 40=64+(2+2*k)
  extent : t.index 41=2+2*k
  order : t.index 42=k
  side : t.index 43=tag
  word : ∀ j < 2+2*k, t.index (64+(2+2*k)+j)=words j

theorem stageRequest_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (tag k : ℕ) (hbit : tag ≤ 1)
    (h0 : s.index 0=tag) (h1 : s.index 1=k) (hsum : s.data 3=s.data 1+s.data 2)
    (hs : Good P s) (hone : P 1) (hv : ∀ j ≤ k, P (j:K)) :
    ∃ t, Block.Eval (Good P) stageRequest s (stageCost k) t ∧ Buffered tag k s.index t ∧
      ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 6 → t.data i=s.data i := by
  let len := 2+2*k
  let base := 64+len
  have lb : 4 ≤ base := by dsimp [base]; omega
  have sep : len ≤ base := by dsimp [base]; omega
  have z : P 0 := by simpa using hv 0 (by omega)
  obtain ⟨a,ea,a0,a3,a5,a6,ai0,ai,af⟩ := saveTag_spec P s tag hbit h0 hs z hone
  obtain ⟨b,eb,bi1,b5,bi,bf⟩ := consumeOrder_spec P a k ai0
    ((ai _ (by decide)).trans h1) a5 a3 ea.safe_end hv
  obtain ⟨c,ec,cbase,ci1,_,ci,cf⟩ := prepareFreshAddress_spec P b k bi1
    ((bf _ (by decide)).trans a0) b5 ((bf _ (by decide)).trans a3) eb.safe_end hv
  have c0 : c.index 0=base := by dsimp [base,len]; omega
  have original (i : ℕ) (hi : 2 ≤ i) : c.index i=s.index i :=
    (ci i (by omega) (by omega)).trans ((bi i (by omega)).trans (ai i (by omega)))
  obtain ⟨d,ed,dd,di0,dtag,dorder,dr2,dr3,draw⟩ := shieldPrefix_spec P c base tag lb hbit c0
    ((cf _ (by decide)).trans ((bf _ (by decide)).trans a6))
    ((cf _ (by decide)).trans ((bf _ (by decide)).trans a3)) ec.safe_end
  obtain ⟨e,ee,de,ei3,ei2,ef⟩ := prepareEnd_spec P d len di0 ed.safe_end
  have early (i : ℕ) (hi : i < 4) : e.index (base+i)=s.index i := by
    rw [ef _ (by omega) (by omega)]
    interval_cases i
    · simpa [h0] using dtag
    · simpa [h1,ci1] using dorder
    · exact dr2.trans (original 2 (by decide))
    · exact dr3.trans (original 3 (by decide))
  have unread (i : ℕ) (hlo : 4 ≤ i) (hi : i < len) : e.index i=s.index i :=
    (ef i (by omega) (by omega)).trans ((draw i hlo (by omega)).trans (original i (by omega)))
  obtain ⟨f,fe,df,fi3,front,rest⟩ := copyTail_spec P e base len lb sep
    ((ef 0 (by decide) (by decide)).trans di0) ei2 ei3 ee.safe_end
  have reading (i : ℕ) (hi : i < len) : f.index (base+i)=s.index i := by
    by_cases hlo : i < 4
    · exact (front i hlo).trans (early i hlo)
    · exact (rest i (by omega) hi).trans (unread i (by omega) hi)
  have same (i : ℕ) (i0 : i ≠ 0) (i3 : i ≠ 3) (i5 : i ≠ 5) (i6 : i ≠ 6) :
      f.data i=s.data i := by
    rw [df,de,dd,cf i i0,bf i i5,af i i0 i3 i5 i6]
  have fs1 := same 1 (by decide) (by decide) (by decide) (by decide)
  have fs2 := same 2 (by decide) (by decide) (by decide) (by decide)
  have fsn : f.data 1+f.data 2=s.data 3 := by rw [fs1,fs2,hsum]
  obtain ⟨t,et,t40,t41,t42,t43,ti,t3,tf⟩ :=
    exposeBuffer_spec P f len fi3 fe.safe_end (fsn ▸ hs 3)
  refine ⟨t, ea.seq (eb.seq (ec.seq (ed.seq (ee.seq (fe.seq et))))), ⟨t40,t41,?_,?_,?_⟩,?_⟩
  · exact t42.trans ((reading 1 (by dsimp [len]; omega)).trans h1)
  · have l0 : 0 < len := by dsimp [len]; omega
    exact t43.trans ((by simpa using reading 0 l0 : f.index base=s.index 0).trans h0)
  · intro j hj
    have high : 64 ≤ base+j := (Nat.le_add_right 64 len).trans (Nat.le_add_right base j)
    exact (ti (base+j) high).trans (reading j hj)
  · intro i i0 i5 i6
    by_cases i3 : i=3
    · subst i; exact t3.trans fsn
    · exact (tf i i3).trans (same i i0 i3 i5 i6)

open OracleSpec.MinorLog

/-- The canonical request supplied by the sealed statement contains the tag and the
order in its first two words, followed by exactly twice that many genuine index words. -/
theorem wire_layout {d e n : ℕ} (u : RawIndex d e n) :
    ∃ tag ≤ 1, ∃ k ≤ n, (words u).length=2+2*k ∧
      (words u)[0]?=some tag ∧ (words u)[1]?=some k := by
  cases u with
  | inl z =>
    refine ⟨0,by decide,z.order,by have h := z.order.isLt; omega,?_,rfl,rfl⟩
    simp [words,squareWords]; omega
  | inr z =>
    refine ⟨1,by decide,z.order,by have h := z.order.isLt; omega,?_,rfl,rfl⟩
    simp [words,squareWords]; omega

/-- Execution at the actual public resume convention. The matrix entries and all
generator records are retained, regardless of the previous use of the address bank. -/
theorem stageRequest_resume {d e n : ℕ} (u : RawIndex d e n) (s : State ℚ)
    (P : ℚ → Prop) (hs : ∀ i, P (s.data i)) (hsum : s.data 3=s.data 1+s.data 2)
    (hone : P 1) (hv : ∀ j ≤ n, P (j:ℚ)) :
    ∃ tag ≤ 1, ∃ k ≤ n, ∃ t, Block.Eval (Good P) stageRequest (resume s (words u)).memory
        (stageCost k) t ∧ Buffered tag k (resume s (words u)).index t ∧
      ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 6 → t.data i=s.data i := by
  obtain ⟨tag,hbit,k,hk,_,h0,h1⟩ := wire_layout u
  obtain ⟨t,run,buffer,frame⟩ := stageRequest_spec P (resume s (words u)).memory tag k hbit
    (by simp [resume,State.memory,h0]) (by simp [resume,State.memory,h1]) hsum hs hone
    (fun j hj => hv j (hj.trans hk))
  exact ⟨tag,hbit,k,hk,t,run,buffer,frame⟩

end Ingress
end Compression
end LinearProgramming
end Optimization
end OAI
