import OAI.Optimization.LinearProgramming.Geometry.BorderLayout
import OAI.Optimization.LinearProgramming.Geometry.BorderStream
import OAI.Optimization.LinearProgramming.Geometry.UniformGramLayout

/-! Initialization of the shared row-selector list and the two address-table cursors. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM Matrix
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {r n k : ℕ}

def prepareRows : Block := .seq (.op (.incr 7 128)) (.seq (indexMoves [(4,141),(5,136)])
  (.seq (.forRange 1 7 (selectorCell false)) (indexMoves [(3,140),(4,142)])))

structure RowsEnd (L : Layout r n) (k : ℕ) (s t : Memory K) : Prop where
  data : t.data=s.data
  minorSize : t.index 7=k+1
  head : t.index 3=L.headers
  cols : t.index 4=L.cols
  rows : ∀ i : Fin (k+1), t.index (L.rows+i.val)=i.val
  frame : ∀ p, 8 ≤ p → (p < L.rows ∨ L.rows+k+1 ≤ p) → t.index p=s.index p

theorem prepareRows_spec (P : K → Prop) (s : Memory K) (hs : s.AllData P) (L : Layout r n)
    (D : Matrix (Fin r) (Fin n) K) (hr : k+1 ≤ r) (J : Fin k → Fin n) (ready : L.Ready D J s) :
    ∃ t, Block.Eval (Memory.AllData P) prepareRows s ((k+1)*7+7) t ∧ RowsEnd L k s t := by
  have hpg := L.pivots_ge
  have hpe := L.pivots_end
  have hhe := L.headers_end
  let a := s.putIndex 7 (s.index 128+1)
  have ea := Block.Eval.op_incr (safe := Memory.AllData P) s 7 128 hs hs
  let init : List (ℕ × ℕ) := [(4,141),(5,136)]
  let b := movedIndices a init
  have eb := indexMoves_eval P a ea.safe_end init
  have bf (p : ℕ) (h4 : p≠4) (h5 : p≠5) (h7 : p≠7) : b.index p=s.index p := by
    simp [b,a,init,movedIndices,h4,h5,h7]
  have b7 : b.index 7=k+1 := by simp [b,a,init,movedIndices,ready.prefixCount]
  have b4 : b.index 4=L.rows := by simp [b,a,init,movedIndices,ready.rowAddr]
  have b5 : b.index 5=L.pivots := by simp [b,a,init,movedIndices,ready.pivotAddr]
  obtain ⟨c, ec, hc⟩ := selectorStream_spec P b eb.safe_end false L.pivots L.rows (k+1) b5 b4 b7 hpg (by omega)
  have cf (p : ℕ) (hp : 8 ≤ p) (ho : p<L.rows ∨ L.rows+k+1≤p) : c.index p=s.index p :=
    (hc.frame p (by omega) (by omega) (by omega) (by omega) (by omega)).trans (bf p (by omega) (by omega) (by omega))
  let last : List (ℕ × ℕ) := [(3,140),(4,142)]
  let t := movedIndices c last
  have et := indexMoves_eval P c ec.safe_end last
  have tf (p : ℕ) (h3 : p≠3) (h4 : p≠4) : t.index p=c.index p := by simp [t,last,movedIndices,h3,h4]
  refine ⟨t, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert ea.seq (eb.seq (ec.seq et)) using 1 <;> simp [prepareRows,init,last]
    omega
  · exact (movedIndices_data c last).trans (hc.data.trans (movedIndices_data a init))
  · rw [tf 7 (by decide) (by decide), hc.frame 7 (by decide) (by decide) (by decide) (by decide) (Or.inl (by omega)), b7]
  · have h := (cf 140 (by decide) (Or.inl (by omega))).trans ready.headerAddr
    simpa [t,last,movedIndices] using h
  · have h := (cf 142 (by decide) (Or.inl (by omega))).trans ready.colAddr
    simpa [t,last,movedIndices] using h
  · intro i
    rw [tf _ (by omega) (by omega)]
    exact hc.words i.val i.isLt
  · intro p hp ho
    rw [tf p (by omega) (by omega), cf p hp ho]

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
