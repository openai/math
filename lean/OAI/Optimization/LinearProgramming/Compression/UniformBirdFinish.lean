import OAI.Optimization.LinearProgramming.Compression.UniformBirdCellData
import OAI.Optimization.LinearProgramming.Compression.UniformIndex

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- Complete a cell from the two accumulated sums and write it in row-major order. -/
def uniformBirdFinish : Block :=
  .seq (cellAddress 8 9 10 1 0 4 5) (.seq birdFinishArithmetic (.seq
    (cellAddress 8 9 10 3 0 4 5) (.op (.store 8 6))))

theorem uniformBirdFinish_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (n : ℕ) (i j : Fin n)
    (hn : m.index 0 = n) (hi : m.index 4 = i.val) (hj : m.index 5 = j.val)
    (hm : ∀ p, P (m.data p)) (hzero : P 0) (hneg : P (-m.data 1))
    (hprod : P (-m.data 1 * m.data (m.index 1 + i.val*n + j.val)))
    (hout : P (-m.data 1 * m.data (m.index 1 + i.val*n + j.val) + m.data 2)) :
    ∃ k t, k ≤ 100*(n+1)^2 ∧ Block.Eval (fun s => ∀ p, P (s.data p)) uniformBirdFinish m k t ∧
      t.data (m.index 3 + i.val*n + j.val) = -m.data 1 * m.data (m.index 1 + i.val*n + j.val) + m.data 2 ∧
      (∀ p, 7 ≤ p → p ≠ m.index 3+i.val*n+j.val → t.data p = m.data p) ∧
      birdCellIndexFrame t m := by
  let PP := fun f : ℕ → K => ∀ p, P (f p)
  have hs : CellScratchOK 8 9 10 0 4 5 := by
    refine ⟨by decide, by decide, by decide, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  let cost := i.val * (4*n+5) + 4*j.val + 5
  obtain ⟨a, ha, had, haf, haddr⟩ := cellAddress_spec PP m hm 8 9 10 1 0 4 5 hs
  rw [hi, hj, hn] at ha haddr
  have hav : a.data (a.index 8) = m.data (m.index 1 + i.val*n + j.val) := by rw [had, haddr]
  obtain ⟨b, hb, hb6, hbf, hbi⟩ := birdFinishArithmetic_spec P a (had ▸ hm) hzero
    (by rw [had]; exact hneg) (by rw [hav, had]; exact hprod) (by rw [hav, had]; exact hout)
  rw [hav, had] at hb6
  have fb (p : ℕ) (h8 : p ≠ 8) (h9 : p ≠ 9) (h10 : p ≠ 10) : b.index p = m.index p := by
    rw [hbi]; exact haf p h8 h9 h10
  obtain ⟨c, hc, hcd, hcf, hc8⟩ := cellAddress_spec PP b hb.safe_end 8 9 10 3 0 4 5 hs
  have hn' : b.index 0 = n := (fb 0 (by decide) (by decide) (by decide)).trans hn
  have hi' : b.index 4 = i.val := (fb 4 (by decide) (by decide) (by decide)).trans hi
  have hj' : b.index 5 = j.val := (fb 5 (by decide) (by decide) (by decide)).trans hj
  rw [hn', hi', hj'] at hc hc8
  rw [fb 3 (by decide) (by decide) (by decide)] at hc8
  let t := c.putData (c.index 8) (c.data 6)
  have ht : ∀ p, P (t.data p) := birdScalarPut hc.safe_end _ _ (hc.safe_end 6)
  have hstore : Block.Eval (fun s => ∀ p, P (s.data p)) (.op (.store 8 6)) c 1 t :=
    Block.Eval.op_store c 8 6 hc.safe_end ht
  refine ⟨cost+(5+(cost+1)), t, ?_, ha.seq (hb.seq (hc.seq hstore)), ?_, ?_, ?_⟩
  · have hrow := Nat.mul_le_mul_right (4*n+5) i.isLt.le
    have hcol := j.isLt.le
    dsimp [cost]; nlinarith
  · simp [t, Memory.putData, hc8, hcd, hb6]
  · intro p hp hdest
    simp only [t, Memory.putData, hc8, Function.update_of_ne hdest, hcd]
    rw [hbf p (by omega) (by omega), had]
  · intro p _ h8 h9 h10
    exact (hcf p h8 h9 h10).trans (fb p h8 h9 h10)

end Compression
end LinearProgramming
end Optimization
end OAI
