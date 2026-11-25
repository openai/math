import OAI.Optimization.LinearProgramming.RAM.Loops
import Mathlib.Tactic

/-! The RPC packet is serialized in sorted column order, using only comparisons of
address registers and a bounded scan of the existing pivot table. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

variable {K : Type*}

open RAM RAM.Block

/-- Set flag 94 when two address words agree. -/
def markEqual (a b : ℕ) : Block :=
  .branch (.addrLT a b) .skip (.branch (.addrLT b a) .skip (.op (.addrConst 94 1)))

private theorem mark_eval {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (hm : ∀ i, P (m.data i)) (a b : ℕ) :
    ∃ cost ≤ 3, Eval (fun s => ∀ i, P (s.data i)) (markEqual a b) m cost
      (if m.index a = m.index b then m.putIndex 94 1 else m) := by
  rcases lt_trichotomy (m.index a) (m.index b) with h | h | h
  · refine ⟨2,by decide,?_⟩
    rw [ite_eq_right h.ne]
    exact Eval.branchTrue (by simp [Cond.test,h]) (.skip hm)
  · refine ⟨3,by decide,?_⟩
    rw [ite_eq_left h]
    exact Eval.branchFalse (by simp [Cond.test,h]) (Eval.branchFalse (by simp [Cond.test,h]) (Eval.op_addrConst m 94 1 hm hm))
  · refine ⟨3,by decide,?_⟩
    rw [ite_eq_right h.ne']
    exact Eval.branchFalse (by simp [Cond.test,h.not_gt]) (Eval.branchTrue (by simp [Cond.test,h]) (.skip hm))

/-- Address 91 is the candidate in ascending serialization order and address 90 is the
appended column of this particular requested minor. -/
def membershipBlock : Block :=
  .seq (.op (.addrConst 94 0)) <| .seq (markEqual 90 91) <| .seq (.op (.addrCopy 92 136)) <|
    .forRange 97 128 (.seq (.op (.addrLoad 93 92)) (.seq (markEqual 93 91) (.op (.incr 92 92))))

def seen (m : Memory K) (i : ℕ) : Prop :=
  m.index 90 = m.index 91 ∨ ∃ j < i, m.index (m.index 136+j) = m.index 91

instance (m : Memory K) (i : ℕ) : Decidable (seen m i) :=
  decidable_of_iff (m.index 90=m.index 91 ∨ ∃ q : Fin i, m.index (m.index 136+q.val)=m.index 91)
    (by simp [seen,Fin.exists_iff])

private theorem seen_succ (m : Memory K) (i : ℕ) :
    seen m (i+1) ↔ seen m i ∨ m.index (m.index 136+i) = m.index 91 := by
  unfold seen
  constructor
  · rintro (h | ⟨q,hq,h⟩)
    · exact Or.inl (Or.inl h)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
      · exact Or.inl (Or.inr ⟨q,hq,h⟩)
      · exact Or.inr h
  · rintro ((h | ⟨q,hq,h⟩) | h)
    · exact Or.inl h
    · exact Or.inr ⟨q,by omega,h⟩
    · exact Or.inr ⟨i,by omega,h⟩

private structure MembershipInv (m : Memory K) (i : ℕ) (s : Memory K) : Prop where
  data : s.data = m.data
  counter : s.index 97 = i
  ptr : s.index 92 = m.index 136 + i
  flag : s.index 94 = if seen m i then 1 else 0
  frame (a) : a ≠ 92 → a ≠ 93 → a ≠ 94 → a ≠ 97 → s.index a = m.index a

/-- The address comparisons write one exactly on a selected column. The full scalar memory,
including the partially serialized output packet, is preserved. -/
theorem membershipBlock_eval {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (m : Memory K) (P : K → Prop) (hm : ∀ i, P (m.data i)) (hbase : 128 ≤ m.index 136) :
    ∃ t cost, cost ≤ 8*m.index 128+7 ∧ Eval (fun s => ∀ i, P (s.data i)) membershipBlock m cost t ∧
      t.data = m.data ∧ (t.index 94 = if seen m (m.index 128) then 1 else 0) ∧
      ∀ a, a ≠ 92 → a ≠ 93 → a ≠ 94 → a ≠ 97 → t.index a = m.index a := by
  classical
  let s0 := m.putIndex 94 0
  let s1 := if m.index 90=m.index 91 then s0.putIndex 94 1 else s0
  let s2 := s1.putIndex 92 (m.index 136)
  have e0 := Eval.op_addrConst (safe := fun s => ∀ i, P (s.data i)) m 94 0 hm hm
  obtain ⟨t0,ht0,e1⟩ := mark_eval P s0 hm 90 91
  change Eval _ _ _ t0 s1 at e1
  have eqd : s1.data = m.data := by dsimp [s1]; split <;> rfl
  have eqf (p : ℕ) (hp : p≠94) : s1.index p=m.index p := by
    dsimp [s1]; split <;> simp [s0,hp]
  have hflag : s1.index 94 = if seen m 0 then 1 else 0 := by
    by_cases h : m.index 90=m.index 91 <;> simp [s1,s0,h,seen]
  have e2 : Eval (fun s => ∀ i, P (s.data i)) (.op (.addrCopy 92 136)) s1 1 s2 := by
    simpa only [s2,eqf 136 (by decide)] using Eval.op_addrCopy s1 92 136 e1.safe_end e1.safe_end
  have init : MembershipInv m 0 (s2.putIndex 97 0) := by
    refine ⟨eqd,by simp,by simp [s2],?_,?_⟩
    · simpa [s2] using hflag
    · intro a h2 _ h4 h7; simp [s2,h2,h7,eqf a h4]
  obtain ⟨t,k,hk,run,ht⟩ := Eval.forRange_invariant
    (body := .seq (.op (.addrLoad 93 92)) (.seq (markEqual 93 91) (.op (.incr 92 92))))
    97 128 (m.index 128) 5 (MembershipInv m) s2 e2.safe_end init
    (fun _ _ h => ⟨h.data ▸ hm,h.counter,h.frame 128 (by decide) (by decide) (by decide) (by decide)⟩) (by
      intro i _ s h
      let p := m.index 136+i
      have hp : 128 ≤ p := by dsimp [p]; omega
      let a := s.putIndex 93 (m.index p)
      have addr : s.index (s.index 92) = m.index p := by
        rw [h.ptr]; exact h.frame p (by omega) (by omega) (by omega) (by omega)
      have hs : ∀ r, P (s.data r) := h.data ▸ hm
      have ea : Eval (fun s => ∀ r, P (s.data r)) (.op (.addrLoad 93 92)) s 1 a := by
        simpa only [a,addr] using Eval.op_addrLoad s 93 92 hs hs
      obtain ⟨c,hc,eq⟩ := mark_eval P a hs 93 91
      let b := if m.index p = m.index 91 then a.putIndex 94 1 else a
      have key : a.index 93 = m.index p := by simp [a]
      have target : a.index 91 = m.index 91 := by simpa [a] using h.frame 91 (by decide) (by decide) (by decide) (by decide)
      rw [key,target] at eq
      change Eval _ _ _ c b at eq
      let dst := b.putIndex 92 (p+1)
      have bp (r : ℕ) (hne : r≠94) : b.index r=a.index r := by
        dsimp [b]; split <;> simp [hne]
      have eb : Eval (fun s => ∀ r, P (s.data r)) (.op (.incr 92 92)) b 1 dst := by
        simpa [dst,bp 92 (by decide),a,h.ptr,p] using Eval.op_incr b 92 92 eq.safe_end eq.safe_end
      have bd : b.data=s.data := by dsimp [b]; split <;> rfl
      refine ⟨dst,1+(c+1),by omega,ea.seq (eq.seq eb),?_,⟩
      refine ⟨bd.trans h.data,?_,?_,?_,?_⟩
      · simp [dst,bp 97 (by decide),a,h.counter]
      · simp [dst,p,Nat.add_assoc]
      · by_cases e : m.index p=m.index 91
        · have hseen : seen m (i+1) := (seen_succ ..).mpr (Or.inr e)
          simp [dst,b,e,hseen]
        · have eqseen : seen m (i+1) ↔ seen m i := (seen_succ ..).trans (or_iff_left e)
          simp [dst,b,e,a,h.flag,eqseen]
      · intro r h2 h3 h4 h7; simp [dst,h2,h7,bp r h4,a,h3,h.frame r h2 h3 h4 h7])
  refine ⟨t,1+(t0+(1+k)),by omega,e0.seq (e1.seq (e2.seq run)),ht.data,ht.flag,ht.frame⟩

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
