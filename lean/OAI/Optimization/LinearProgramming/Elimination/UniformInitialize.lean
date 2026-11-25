import OAI.Optimization.LinearProgramming.Elimination.UniformFlag
import OAI.Optimization.LinearProgramming.RAM.Loops

/-! A fixed RAM loop clears the active-column flags and preserves all other arrays. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open RAM

def clearFlags : Block := .forRange 19 0 (writeFlag 0)

def clearFlagsCost (n : ℕ) := n*((4*n+7)+3)+2

theorem clearFlags_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (n f : ℕ) (hn : m.index 0=n) (hz : m.index 14=0)
    (hf : m.index 18=f) (hbase : 7 ≤ f) (hm : ∀p,P (m.data p)) (h0 : P 0) :
    ∃ t c,c ≤ clearFlagsCost n ∧ Block.Eval (fun w => ∀ i,P (w.data i)) clearFlags m c t ∧
      (∀ i : Fin n, t.data (f+i.val)=0) ∧
      (∀ p,p≠8 → p≠9 → p≠10 → p≠19 → t.index p=m.index p) ∧
      ∀ p,7≤p → (p<f ∨ f+n≤p) → t.data p=m.data p := by
  let I (k : ℕ) (s : Memory K) := (∀p,P (s.data p)) ∧ s.index 19=k ∧
    (∀ p,p≠8 → p≠9 → p≠10 → p≠19 → s.index p=m.index p) ∧
    (∀ p,7≤p → (p<f ∨ f+n≤p) → s.data p=m.data p) ∧
    ∀ i : Fin n,i.val<k → s.data (f+i.val)=0
  have ini : I 0 (m.putIndex 19 0) :=
    ⟨hm,by simp,fun p _ _ _ h => Memory.putIndex_ne _ h _,fun _ _ _ =>rfl,fun _ h => by omega⟩
  have adv (k : ℕ) (hk : k<n) (s : Memory K) (h : I k s) :
      ∃ t c,c≤4*n+7 ∧ Block.Eval (fun w => ∀i,P (w.data i)) (writeFlag 0) s c t ∧
        I (k+1) (t.putIndex 19 (t.index 19+1)) := by
    let j : Fin n := ⟨k,hk⟩
    have fptr : s.index 18=f := (h.2.2.1 18 (by decide) (by decide) (by decide) (by decide)).trans hf
    obtain ⟨t,c,hc,he,v,fd,fi⟩ := writeFlag_spec P s 0 n j
      ((h.2.2.1 14 (by decide) (by decide) (by decide) (by decide)).trans hz) h.2.1 h.1 (by simpa using h0)
    rw [fptr] at v fd
    have tk : t.index 19=k := (fi 19 (by decide) (by decide) (by decide)).trans h.2.1
    refine ⟨t,c,hc,he,he.safe_end,by simp [tk],fun p a b d e =>
      (Memory.putIndex_ne _ e _).trans ((fi p a b d).trans (h.2.2.1 p a b d e)),?_,?_⟩
    · intro p hp hp'; exact (fd p hp (by change p≠f+k; omega)).trans (h.2.2.2.1 p hp hp')
    · intro i hi
      change t.data (f+i.val)=0
      by_cases hki : i.val=k
      · simpa [j,hki] using v
      · have h7 : 7≤f+i.val := by omega
        exact (fd _ h7 (by change f+i.val≠f+k; omega)).trans (h.2.2.2.2 i (by omega))
  obtain ⟨t,c,hc,he,ht⟩ := Block.Eval.forRange_invariant (body:=writeFlag 0) 19 0 n (4*n+7)
    I m hm ini (fun _ _ h => ⟨h.1,h.2.1,(h.2.2.1 0 (by decide) (by decide) (by decide) (by decide)).trans hn⟩) adv
  exact ⟨t,c,hc,he,fun i=>ht.2.2.2.2 i i.isLt,ht.2.2.1,ht.2.2.2.1⟩

end Elimination
end LinearProgramming
end Optimization
end OAI
