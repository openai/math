import OAI.Optimization.LinearProgramming.Compression.ServiceReadHeader
import OAI.Optimization.LinearProgramming.Compression.ServiceAddressPlan
import OAI.Optimization.LinearProgramming.RAM.Array

/-! Primitive transfer of constructed exponents into the cache's address registers. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- Scalar 4 contains the constructed cutoff exponent and scalar 3 contains the
precision exponent. Counting against each writes the two address values without
looking at any scalar bits. -/
def proxyExponentCounters : Block := .seq (headerToAddress 4 1) (headerToAddress 3 2)

theorem proxyExponentCounters_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (fuel prec : ℕ) (hf : s.data 4 = (fuel:K))
    (hk : s.data 3 = (prec:K)) (hs : s.AllData P) (h1 : P 1)
    (hn : ∀ j ≤ max fuel prec, P (j:K)) :
    ∃ t, Block.Eval (Memory.AllData P) proxyExponentCounters s ((4*fuel+4)+(4*prec+4)) t ∧
      t.index 1 = fuel ∧ t.index 2 = prec ∧
      (∀ i, i≠1 → i≠2 → t.index i = s.index i) ∧
      ∀ i, i≠0 → i≠6 → t.data i = s.data i := by
  obtain ⟨a,ea,a1,ai,ad⟩ := headerToAddress_spec P s 4 1 fuel (by decide) (by decide)
    hf hs h1 (fun j hj => hn j (hj.trans (le_max_left _ _)))
  obtain ⟨t,et,t2,ti,td⟩ := headerToAddress_spec P a 3 2 prec (by decide) (by decide)
    ((ad 3 (by decide) (by decide)).trans hk) ea.safe_end h1
    (fun j hj => hn j (hj.trans (le_max_right _ _)))
  exact ⟨t,ea.seq et,(ti 1 (by decide)).trans a1,t2,
    fun i h₁ h₂ => (ti i h₂).trans (ai i h₁),fun i h₀ h₆ => (td i h₀ h₆).trans (ad i h₀ h₆)⟩

/-- The initializer may have written over address 60. Its incoming value was
saved in address 4, the incoming protected extent in address 6, and the end of
the new parameter tape is returned in address 2. -/
def proxyRestoreWatermark : Block := .seq (.op (.addrCopy 60 4))
  (.branch (.addrLT 6 2) (.op (.addrCopy 4 2)) (.op (.addrCopy 4 6)))

theorem proxyRestoreWatermark_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (hs : s.AllData P) :
    ∃ t l, l ≤ 4 ∧ Block.Eval (Memory.AllData P) proxyRestoreWatermark s l t ∧
      t.data = s.data ∧ t.index 60 = s.index 4 ∧ t.index 4 = max (s.index 6) (s.index 2) ∧
      ∀ i, i≠4 → i≠60 → t.index i = s.index i := by
  let a := s.putIndex 60 (s.index 4)
  have ea : Block.Eval (Memory.AllData P) (.op (.addrCopy 60 4)) s 1 a :=
    Block.Eval.op_addrCopy _ _ _ hs hs
  by_cases h : s.index 6 < s.index 2
  · let t := a.putIndex 4 (a.index 2)
    have et : Block.Eval (Memory.AllData P) (.op (.addrCopy 4 2)) a 1 t :=
      Block.Eval.op_addrCopy _ _ _ hs hs
    refine ⟨t,4,le_rfl,ea.seq (.branchTrue (by simpa [Cond.test,a] using h) et),rfl,?_,?_,?_⟩
    · simp [t,a]
    · simp [t,a,max_eq_right h.le]
    · intro i hi hi'; simp [t,a,hi,hi']
  · let t := a.putIndex 4 (a.index 6)
    have et : Block.Eval (Memory.AllData P) (.op (.addrCopy 4 6)) a 1 t :=
      Block.Eval.op_addrCopy _ _ _ hs hs
    refine ⟨t,3,by decide,ea.seq (.branchFalse (by simpa [Cond.test,a] using h) et),rfl,?_,?_,?_⟩
    · simp [t,a]
    · simp [t,a,max_eq_left (le_of_not_gt h)]
    · intro i hi hi'; simp [t,a,hi,hi']

end Compression
end LinearProgramming
end Optimization
end OAI
