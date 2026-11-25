import OAI.Optimization.LinearProgramming.Compression.ServiceGeneratorTable

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

variable {K : Type*} {d e n : ℕ}

def publicWords (u : PairMinorIndex d e n) : List ℕ :=
  tag u :: order u :: (List.ofFn (fun i : Fin (order u) => rowWord u i.val) ++
    List.ofFn (fun i : Fin (order u) => colWord u i.val))

theorem publicWords_length (u : PairMinorIndex d e n) : (publicWords u).length = 2+2*order u := by
  simp [publicWords]; omega


theorem row_get (u : PairMinorIndex d e n) (j : ℕ) (hj : j < order u) :
    (publicWords u)[2+j]?.getD 0 = rowWord u j := by
  rw [show 2+j = j+2 by omega]
  simp only [publicWords,List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by simpa using hj),List.getElem?_ofFn]
  simp [hj]

theorem col_get (u : PairMinorIndex d e n) (j : ℕ) (hj : j < order u) :
    (publicWords u)[2+order u+j]?.getD 0 = colWord u j := by
  rw [show 2+order u+j = (order u+j)+2 by omega]
  simp only [publicWords,List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by simp),List.length_ofFn,List.getElem?_ofFn]
  simp [hj]

theorem tag_le (u : PairMinorIndex d e n) : tag u ≤ 1 := by cases u <;> simp [tag]

theorem row_padding (u : PairMinorIndex d e n) (j : ℕ) (hj : order u ≤ j) : rowWord u j = 0 := by
  cases u <;> simp_all [order,rowWord]

theorem col_padding (u : PairMinorIndex d e n) (j : ℕ) (hj : order u ≤ j) : colWord u j = 0 := by
  cases u <;> simp_all [order,colWord]

/-- The only words read by the scalar staging program, with their actual external meaning. -/
structure Wire (u : PairMinorIndex d e n) (s : Memory K) : Prop where
  base : 40 ≤ s.index 40
  side : s.index 43 = tag u
  size : s.index 42 = order u
  rows : ∀ i < order u,s.index (s.index 40+2+i) = rowWord u i
  cols : ∀ i < order u,s.index (s.index 40+2+order u+i) = colWord u i

/-- A safe copy of the entire public word prefix supplies the four cursor facts used below. -/
theorem Wire.of_canonical {u : PairMinorIndex d e n} {s : Memory K}
    (hb : 40 ≤ s.index 40) (ht : s.index 43 = tag u) (hk : s.index 42 = order u)
    (hw : ∀j < 2+2*order u,s.index (s.index 40+j) = (publicWords u)[j]?.getD 0) : Wire u s := by
  refine ⟨hb,ht,hk,?_,?_⟩
  · intro i hi
    simpa [Nat.add_assoc] using (hw (2+i) (by omega)).trans (row_get u i hi)
  · intro i hi
    simpa [Nat.add_assoc] using (hw (2+order u+i) (by omega)).trans (col_get u i hi)

theorem Wire.frame {u : PairMinorIndex d e n} {s t : Memory K} (h : Wire u s)
    (idx : ∀a,40 ≤ a → t.index a = s.index a) : Wire u t := by
  have hb := idx 40 (by decide)
  refine ⟨hb ▸ h.base,(idx 43 (by decide)).trans h.side,(idx 42 (by decide)).trans h.size,?_,?_⟩
  · intro i hi; rw [hb,idx _ (by have := h.base; omega),h.rows i hi]
  · intro i hi; rw [hb,idx _ (by have := h.base; omega),h.cols i hi]

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
