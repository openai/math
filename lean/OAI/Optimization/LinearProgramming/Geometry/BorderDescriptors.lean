import OAI.Optimization.LinearProgramming.Geometry.BorderRows
import OAI.Optimization.LinearProgramming.Geometry.BorderTable

/-! Prepare all signed determinant batches from the original matrix, pivot table and layout. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM Matrix Compression.MinorLoad
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {r n k : ℕ}

/-- A single dimension-independent instruction block. The first counted loop emits the
shared identity rows. The second emits every candidate header and ordered column list. -/
def prepareDescriptors : Block := .seq prepareRows (.seq (.forRange 0 130 emitRecord)
  (indexMoves [(16,130),(17,140),(18,143)]))

/-- Exact execution, preservation of the source and the persistent registers, preparation
of the entire determinant-service input, and a frame for the untouched address bank. -/
theorem prepareDescriptors_spec (P : K → Prop) (s : Memory K) (hs : s.AllData P)
    (L : Layout r n) (D : Matrix (Fin r) (Fin n) K) (hr : k+1 ≤ r) (J : Fin k → Fin n)
    (ready : L.Ready D J s) :
    ∃ t, Block.Eval (Memory.AllData P) prepareDescriptors s ((k+1)*7+n*(k*7+22)+12) t ∧
      L.Ready D J t ∧ BatchInput (L.batch D hr J) t ∧ t.data=s.data ∧
      ∀ p, 128≤p → (p<L.headers ∨ L.headers+6*n≤p) → (p<L.rows ∨ L.rows+k+1≤p) →
        (p<L.cols ∨ L.cols+(k+1)*n≤p) → t.index p=s.index p := by
  have hpg := L.pivots_ge
  have hpe := L.pivots_end
  have hhe := L.headers_end
  have hre := L.rows_end
  obtain ⟨a, ea, ha⟩ := prepareRows_spec P s hs L D hr J ready
  have ra : L.Ready D J a := ready.of_frame hr ha.data (fun p hp hi => ha.frame p (by omega) (Or.inl (by omega)))
  obtain ⟨b, eb, hb⟩ := descriptorTable_spec P a ea.safe_end L D hr J ra ha.minorSize ha.head ha.cols
  let out : List (ℕ × ℕ) := [(16,130),(17,140),(18,143)]
  let t := movedIndices b out
  have et := indexMoves_eval P b eb.safe_end out
  have df : t.data=b.data := movedIndices_data b out
  have tf (p : ℕ) (hp : 128≤p) : t.index p=b.index p := by simp [t,out,movedIndices,show p≠16 by omega,show p≠17 by omega,show p≠18 by omega]
  have rt : L.Ready D J t := hb.ready.of_frame hr df (fun p hp _ => tf p hp)
  refine ⟨t, ?_,rt, ?_, df.trans (hb.data.trans ha.data), ?_⟩
  · convert ea.seq (eb.seq et) using 1 <;> simp [prepareDescriptors,out]
    omega
  · refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [t,out,movedIndices] using hb.ready.width
    · simpa [t,out,movedIndices,Layout.batch] using hb.ready.headerAddr
    · simpa [t,out,movedIndices,Layout.batch] using hb.ready.answerAddr
    · intro j w hw
      exact (tf _ (by change 128≤L.headers+6*j.val+w; omega)).trans (hb.words j j.isLt w hw)
    · intro j i
      have ii : i.val < k+1 := i.isLt
      change t.index (L.rows+i.val)=i.val
      rw [tf _ (by omega), hb.frame _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
      exact ha.rows ⟨i.val, ii⟩
    · intro j i
      exact (tf _ (by change 128≤L.cols+(k+1)*j.val+i.val; omega)).trans (hb.selector j j.isLt i)
    · intro _ i j
      exact rt.matrixData i j
  · intro p hp hh hh' hc
    rw [tf p hp,hb.frame _ (by omega) hh hc,ha.frame _ (by omega) hh']

/-- The exact initialization cost is quadratic in the public matrix dimensions. -/
theorem prepareDescriptors_steps_le (hr : k+1 ≤ r) (n : ℕ) :
    (k+1)*7+n*(k*7+22)+12 ≤ 41*(r+n+1)^2 := by
  calc
    _ ≤ r*7+n*(r*7+22)+12 := by gcongr; omega
    _ ≤ _ := by nlinarith [Nat.zero_le (r*r), Nat.zero_le (r*n), Nat.zero_le (n*n)]

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
