import OAI.Optimization.LinearProgramming.Geometry.UniformGramLayout
import OAI.Optimization.LinearProgramming.RAM.StrideCopy

/-! Load a normal zero-based input tape into retained high storage, including entry zero.
The second copy relocates the dual matrix to a disjoint slot before the primal matrix. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace LabelInput

open RAM
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

structure Copied (m t : Memory K) (src dst count : ℕ) : Prop where
  words : ∀ j<count, t.data (dst+j) = m.data (src+j)
  dataFrame : ∀ a, a≠0 → (a<dst ∨ dst+count≤a) → t.data a=m.data a
  indexFrame : ∀ a, a≠8 → a≠9 → a≠10 → a≠11 → t.index a=m.index a

private def moveWords : Block := StrideCopy.block false 8 9 10 11 0 1 1

private theorem moveWords_spec (P : K → Prop) (m : Memory K) (hm : m.AllData P)
    (src dst count : ℕ) (hs : m.index 8=src) (hd : m.index 9=dst) (hc : m.index 11=count)
    (hsrc : 0<src) (hdst : 0<dst) (hsep : src+count≤dst ∨ dst+count≤src) :
    ∃ t, Block.Eval (Memory.AllData P) moveWords m (7*count+2) t ∧ Copied m t src dst count := by
  obtain ⟨t,e,w,f,_,_,_,g⟩ := StrideCopy.block_correct P m false 8 9 10 11 0 1 1 count hm hc
    (by decide) (by decide) (by simp) (by intro j _; simp [hs]; omega) (by intro j _; simp [hd]; omega)
    (by intro a j ha hj; simp [hd,hs]; omega)
  refine ⟨t, by simpa only [moveWords, Nat.mul_comm] using e, ?_, ?_, ?_⟩
  · simpa [hs,hd] using w
  · intro a h0 hoff
    apply f a h0
    intro j hj
    simp [hd]; omega
  · intro a h8 h9 h10 _
    exact g a h8 h9 h10

/-- Entry zero is already in the scalar scratch register for the first store. Remaining
entries are nonzero-address sources, so all later loads may freely reuse register zero. -/
def copyRaw : Block := .seq (.op (.store 206 0)) (.seq (.op (.addrConst 8 1))
  (.seq (.op (.incr 9 206)) (.seq (.op (.decr 11 224)) moveWords)))

theorem copyRaw_spec (P : K → Prop) (m : Memory K) (hm : m.AllData P) (dst count : ℕ)
    (hd : m.index 206=dst) (hc : m.index 224=count) (hn : 0<count) (hs : count<dst) :
    ∃ t, Block.Eval (Memory.AllData P) copyRaw m (7*(count-1)+6) t ∧ Copied m t 0 dst count := by
  let a := m.putData (m.index 206) (m.data 0)
  have ha : a.AllData P := by
    intro j
    by_cases hj : j=m.index 206
    · simpa [a,hj] using hm 0
    · simpa [a,hj] using hm j
  let b := a.putIndex 8 1
  let c := b.putIndex 9 (b.index 206+1)
  let d := c.putIndex 11 (c.index 224-1)
  have ea := Block.Eval.op_store (safe:=Memory.AllData P) m 206 0 hm ha
  have eb := Block.Eval.op_addrConst (safe:=Memory.AllData P) a 8 1 ha ha
  have ec := Block.Eval.op_incr (safe:=Memory.AllData P) b 9 206 ha ha
  have ed := Block.Eval.op_decr (safe:=Memory.AllData P) c 11 224 ha ha
  obtain ⟨t,run,h⟩ := moveWords_spec P d ha 1 (dst+1) (count-1) (by simp [d,c,b])
    (by simp [d,c,b,a,hd]) (by simp [d,c,b,a,hc]) (by decide) (by omega) (Or.inl (by omega))
  have original (j : ℕ) (hj : j≠dst) : d.data j=m.data j := by simp [d,c,b,a,hd,hj]
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · simpa only [copyRaw,show 1+(1+(1+(1+(7*(count-1)+2))))=7*(count-1)+6 by omega]
      using ea.seq (eb.seq (ec.seq (ed.seq run)))
  · intro j hj
    cases j with
    | zero =>
      simp only [Nat.add_zero]
      rw [h.dataFrame dst (by omega) (Or.inl (by omega))]
      simp [d,c,b,a,hd]
    | succ j =>
      have hw := h.words j (by omega)
      have hj' := original (1+j) (by omega)
      rw [hj'] at hw
      simpa only [Nat.add_assoc,Nat.add_comm 1 j,Nat.zero_add] using hw
  · intro j hj off
    rw [h.dataFrame j hj (by omega), original j (by omega)]
  · intro j j8 j9 j10 j11
    rw [h.indexFrame j j8 j9 j10 j11]
    simp [d,c,b,a,j8,j9,j11]

/-- Copy the dual suffix of the retained input into the disjoint slot before the primal matrix. -/
def copyDual : Block := .seq (indexMoves [(8,225),(9,200),(11,220)]) moveWords

theorem copyDual_spec (P : K → Prop) (m : Memory K) (hm : m.AllData P) (src dst count : ℕ)
    (hs : m.index 225=src) (hd : m.index 200=dst) (hc : m.index 220=count) (h0 : 0<dst)
    (hsep : dst+count≤src) :
    ∃ t, Block.Eval (Memory.AllData P) copyDual m (7*count+5) t ∧ Copied m t src dst count := by
  let regs : List (ℕ × ℕ) := [(8,225),(9,200),(11,220)]
  let a := movedIndices m regs
  have e := indexMoves_eval P m hm regs
  obtain ⟨t,run,h⟩ := moveWords_spec P a e.safe_end src dst count (by simp [a,regs,movedIndices,hs])
    (by simp [a,regs,movedIndices,hd]) (by simp [a,regs,movedIndices,hc]) (by omega) h0 (Or.inr hsep)
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · change Block.Eval _ (.seq (indexMoves regs) _) m (7*count+5) t
    convert e.seq run using 1
    simp [regs]
    omega
  · simpa only [a,movedIndices_data] using h.words
  · simpa only [a,movedIndices_data] using h.dataFrame
  · intro j j8 j9 j10 j11
    rw [h.indexFrame j j8 j9 j10 j11]
    simp [a,regs,movedIndices,j8,j9,j11]

end LabelInput
end Geometry
end LinearProgramming
end Optimization
end OAI
