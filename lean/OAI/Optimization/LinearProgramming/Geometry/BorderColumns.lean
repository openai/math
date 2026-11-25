import OAI.Optimization.LinearProgramming.Geometry.BorderStream
import OAI.Optimization.LinearProgramming.Geometry.UniformGramLayout

/-! The bordered-column selector `J₀,…,Jₖ₋₁,j` is constructed by a fixed RAM block. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def emitColumn : Block := .seq (indexMoves [(5,136),(7,128)])
  (.seq (.forRange 1 7 (selectorCell true)) (.seq (emitWord 4 0) (.op (.incr 7 128))))

structure ColumnEnd (s t : Memory K) (j k src dst : ℕ) : Prop where
  data : t.data = s.data
  cursor : t.index 4 = dst+k+1
  prefixSize : t.index 7 = k+1
  appendWord : t.index (dst+k) = j
  prefixWord : ∀ i < k, t.index (dst+i) = s.index (src+i)
  frame : ∀ p, p ≠ 1 → p ≠ 4 → p ≠ 5 → p ≠ 6 → p ≠ 7 →
    (p < dst ∨ dst+k+1 ≤ p) → t.index p = s.index p

theorem emitColumn_spec (P : K → Prop) (s : Memory K) (hs : s.AllData P)
    (j k src dst : ℕ) (hj : s.index 0 = j) (hk : s.index 128 = k)
    (hsrc : s.index 136 = src) (hdst : s.index 4 = dst) (hlo : 256 ≤ src) (hgap : src+k ≤ dst) :
    ∃ t, Block.Eval (Memory.AllData P) emitColumn s (k*7+7) t ∧ ColumnEnd s t j k src dst := by
  let regs : List (ℕ × ℕ) := [(5,136),(7,128)]
  let u := movedIndices s regs
  have set := indexMoves_eval P s hs regs
  have uframe (p : ℕ) (h5 : p ≠ 5) (h7 : p ≠ 7) : u.index p = s.index p := by
    simp [u, regs, movedIndices, h5,h7]
  have u5 : u.index 5 = src := by simp [u,regs,movedIndices,hsrc]
  have u7 : u.index 7 = k := by simp [u,regs,movedIndices,hk]
  obtain ⟨v, copy, cv⟩ := selectorStream_spec P u set.safe_end true src dst k u5
    ((uframe 4 (by decide) (by decide)).trans hdst) u7 hlo hgap
  have v0 : v.index 0 = j := (cv.frame 0 (by decide) (by decide) (by decide) (by decide) (Or.inl (by omega))).trans
    ((uframe 0 (by decide) (by decide)).trans hj)
  obtain ⟨w, emit, wd, w4, wval, wf⟩ := emitWord_spec P v copy.safe_end 4 0 (by rw [cv.destination]; omega)
  have v128 : v.index 128 = k := (cv.frame 128 (by decide) (by decide) (by decide) (by decide) (Or.inl (by omega))).trans
    ((uframe 128 (by decide) (by decide)).trans hk)
  have w128 : w.index 128 = k := (wf 128 (by decide) (by rw [cv.destination]; omega)).trans v128
  let t := w.putIndex 7 (w.index 128+1)
  have finish := Block.Eval.op_incr (safe := Memory.AllData P) w 7 128 emit.safe_end emit.safe_end
  have run := set.seq (copy.seq (emit.seq finish))
  refine ⟨t, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Block.Eval _ (.seq (indexMoves regs) _) s (k*7+7) t
    convert run using 1
    simp [regs]
    omega
  · exact wd.trans (cv.data.trans (movedIndices_data s regs))
  · rw [show t.index 4 = w.index 4 from Memory.putIndex_ne _ (by decide) _, w4, cv.destination]
  · simp [t,w128]
  · rw [show t.index (dst+k) = w.index (dst+k) from Memory.putIndex_ne _ (by omega) _,
        ← cv.destination, wval, v0]
  · intro i hi
    rw [show t.index (dst+i) = w.index (dst+i) from Memory.putIndex_ne _ (by omega) _,
        wf _ (by omega) (by rw [cv.destination]; omega), cv.words _ hi]
    exact uframe _ (by omega) (by omega)
  · intro p hp1 hp4 hp5 hp6 hp7 hp
    rw [show t.index p = w.index p from Memory.putIndex_ne _ hp7 _,
        wf _ hp4 (by rw [cv.destination]; omega), cv.frame _ hp1 hp4 hp5 hp6 (by omega),
        uframe _ hp5 hp7]

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
