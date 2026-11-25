import OAI.Optimization.LinearProgramming.RAM.Array

/-! Row-major dense matrix-vector multiplication on the fixed scalar/address RAM. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Dense

open scoped BigOperators

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Rewind the vector pointer before scanning a new matrix row, then append the result. -/
def matVecRow : Block :=
  .seq (.op (.addrCopy 21 25))
    (.seq dotBlock (.seq (.op (.store 26 20)) (.op (.incr 26 26))))

/-- 20 holds the matrix pointer, 23 its width, 25 the input vector base, 26 the destination
pointer and 27 its height. Address register 24 counts completed rows. -/
def matVecBlock : Block := .forRange 24 27 matVecRow

def rowTerm (m : Memory K) (cols row col : ℕ) : K :=
  m.data (m.index 20 + row*cols + col) * m.data (m.index 25+col)

def rowPrefix (m : Memory K) (cols row p : ℕ) : K :=
  ∑ col ∈ Finset.range p, rowTerm m cols row col

structure MatVecAt (m : Memory K) (cols rows : Nat) (s : Memory K) : Prop where
  source : s.index 20 = m.index 20 + rows*cols
  dst : s.index 26 = m.index 26 + rows
  cursor : s.index 24 = rows
  cells : ∀ j<rows, s.data (m.index 26 + j) = rowPrefix m cols j cols
  dataFrame : ∀ k, k<20 ∨ 23<k → k<m.index 26 ∨ m.index 26+rows≤k → s.data k=m.data k
  indexFrame : ∀ k, (k<20 ∨ 22<k) → k≠24 → k≠26 → s.index k=m.index k

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem matVec_start (m : Memory K) (c : ℕ) : MatVecAt m c 0 (m.putIndex 24 0) := by
  constructor
  · simp [Memory.putIndex]
  · simp [Memory.putIndex]
  · simp [Memory.putIndex]
  · simp
  · intro k _ _; rfl
  · intro k _ h _
    simp [Memory.putIndex,Function.update_of_ne h]

private theorem matVec_row {P : K → Prop} {m s : Memory K} {r rows cols : ℕ}
    (h : MatVecAt m cols r s) (hr : r<rows) (hs : s.AllData P)
    (hA : 23 < m.index 20) (hx : 23 < m.index 25)
    (hAZ : m.index 20 + rows*cols ≤ m.index 26) (hxZ : m.index 25+cols ≤ m.index 26)
    (hc : m.index 23=cols)
    (hterm : ∀ j<cols, P (rowTerm m cols r j))
    (hprefix : ∀ j≤cols, P (rowPrefix m cols r j)) :
    ∃ t, Block.Eval (Memory.AllData P) matVecRow s (9*cols+6) t ∧
      (t.putIndex 24 (t.index 24+1)).AllData P ∧ MatVecAt m cols (r+1) (t.putIndex 24 (t.index 24+1)) := by
  let s1 := s.putIndex 21 (s.index 25)
  have h1 : s1.AllData P := hs
  have hbase : s.index 25=m.index 25 := h.indexFrame 25 (by omega) (by decide) (by decide)
  have hsrc : s1.index 20=m.index 20+r*cols := by simpa [s1,Memory.putIndex] using h.source
  have hvec : s1.index 21=m.index 25 := by simpa [s1,Memory.putIndex] using hbase
  have hlen : s1.index 23=cols := by
    simpa [s1,Memory.putIndex,hc] using h.indexFrame 23 (by omega) (by decide) (by decide)
  have hol : 23 < m.index 26 := by omega
  have heq (j : ℕ) (hj : j<cols) : dotTerm s1 j = rowTerm m cols r j := by
    have hl₁ : 23 < m.index 20 + r*cols+j := by omega
    have hl₂ : m.index 20+r*cols+j < m.index 26 := by
      have he := Nat.mul_le_mul_right cols hr
      rw [Nat.succ_mul] at he
      omega
    have hr₁ : 23 < m.index 25+j := by omega
    have hr₂ : m.index 25+j < m.index 26 := by omega
    simp only [dotTerm,rowTerm,hsrc,hvec]
    change s.data _ * s.data _ = _
    rw [h.dataFrame _ (Or.inr hl₁) (Or.inl hl₂),h.dataFrame _ (Or.inr hr₁) (Or.inl hr₂)]
  have hsum (j : ℕ) (hj : j≤cols) : dotPrefix s1 j = rowPrefix m cols r j := by
    exact Finset.sum_congr rfl fun k hk => heq k ((Finset.mem_range.mp hk).trans_le hj)
  obtain ⟨u, eu, hu⟩ := dotBlock_correct P s1 cols h1 (by rw [hsrc]; omega) (by rwa [hvec]) hlen
    (fun j hj => (heq j hj) ▸ hterm j hj) (fun j hj => (hsum j hj) ▸ hprefix j hj)
  have hus := eu.safe_end
  have huidx (k : ℕ) (hk : k<20 ∨ 22<k) : u.index k=s.index k := by
    rw [hu.indexFrame k hk]
    simp [s1,Memory.putIndex,Function.update_of_ne (by omega : k ≠ 21)]
  have hptr : u.index 26=m.index 26+r := (huidx 26 (by omega)).trans h.dst
  have hres : u.data 20=rowPrefix m cols r cols := hu.sum.trans (hsum cols le_rfl)
  have hdata (k : ℕ) (hk : k<20 ∨ 23<k) : u.data k=s.data k := hu.dataFrame k hk
  let v := u.putData (u.index 26) (u.data 20)
  let t := v.putIndex 26 (v.index 26+1)
  have hv : v.AllData P := hus.putData _ (hus _)
  have ht : t.AllData P := hv
  have e := Block.Eval.seq (Block.Eval.op_addrCopy s 21 25 hs h1)
    (Block.Eval.seq eu (Block.Eval.seq (Block.Eval.op_store u 26 20 hus hv)
      (Block.Eval.op_incr v 26 26 hv ht)))
  refine ⟨t, ?_, ht, ?_⟩
  · rw [show 9*cols+6 = 1+((9*cols+3)+(1+1)) by ring]
    exact e
  constructor
  · simp [t,v,hu.left,hsrc,Nat.succ_mul,Nat.add_assoc]
  · simp [t,v,Memory.putIndex,Memory.putData,hptr,Nat.add_assoc]
  · simp [t,v,Memory.putIndex,Memory.putData,huidx 24 (by omega),h.cursor]
  · intro j hj
    by_cases hjr : j=r
    · subst j
      simpa [t,v,Memory.putIndex,Memory.putData,hptr] using hres
    · have hj' : j<r := by omega
      have hk : 23 < m.index 26+j := by omega
      have hne : m.index 26+j ≠ u.index 26 := by rw [hptr]; omega
      simpa [t,v,Memory.putIndex,Memory.putData,Function.update_of_ne hne] using
        (hdata _ (Or.inr hk)).trans (h.cells j hj')
  · intro k hk hpos
    have hne : k ≠ u.index 26 := by rw [hptr]; omega
    have hbefore : k<m.index 26 ∨ m.index 26+r ≤ k := by omega
    simpa [t,v,Memory.putIndex,Memory.putData,Function.update_of_ne hne] using
      (hdata _ hk).trans (h.dataFrame _ hk hbefore)
  · intro k hk h24 h26
    simpa [t,v,Memory.putIndex,Memory.putData,Function.update_of_ne h24,Function.update_of_ne h26]
      using (huidx k hk).trans (h.indexFrame _ hk h24 h26)

/-- This program and its register numbers are independent of the matrix dimensions.
Data before the destination, including the original matrix and vector, is preserved
outside the four scratch registers. Zero rows and zero columns are allowed. -/
theorem matVecBlock_correct (P : K → Prop) (m : Memory K) (rows cols : ℕ) (hm : m.AllData P)
    (hA : 23 < m.index 20) (hx : 23 < m.index 25)
    (hAZ : m.index 20 + rows*cols ≤ m.index 26) (hxZ : m.index 25+cols ≤ m.index 26)
    (hc : m.index 23=cols) (hr : m.index 27=rows)
    (hterm : ∀ r<rows, ∀ j<cols, P (rowTerm m cols r j))
    (hsums : ∀ r<rows, ∀ j≤cols, P (rowPrefix m cols r j)) :
    ∃ t, Block.Eval (Memory.AllData P) matVecBlock m (rows*(9*cols+9)+2) t ∧ MatVecAt m cols rows t := by
  obtain ⟨t,et,_,ht⟩ := Block.Eval.forRange_invariant_exact (body := matVecRow)
    24 27 rows (9*cols+6) (fun j s => s.AllData P ∧ MatVecAt m cols j s) m hm
    ⟨hm, matVec_start m cols⟩
    (fun _ _ ⟨hs,h⟩ => ⟨hs,h.cursor,(h.indexFrame 27 (by omega) (by decide) (by decide)).trans hr⟩)
    (fun r hrow _ ⟨hs,h⟩ => matVec_row h hrow hs hA hx hAZ hxZ hc (hterm _ hrow) (hsums _ hrow))
  exact ⟨t,et,ht⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- A fully populated finite row-major input computes the usual matrix-vector product. -/
theorem rowPrefix_eq_mulVec {rows cols : ℕ} (m : Memory K)
    (A : Matrix (Fin rows) (Fin cols) K) (x : Fin cols → K)
    (ha : ∀ r : Fin rows, ∀ j : Fin cols, m.data (m.index 20 + (r:ℕ)*cols + (j:ℕ)) = A r j)
    (hx : ∀ j : Fin cols, m.data (m.index 25 + (j:ℕ)) = x j) (r : Fin rows) :
    rowPrefix m cols r cols = (A.mulVec x) r := by
  rw [rowPrefix, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun j _ => by simp [rowTerm,ha r j,hx j]

end Dense
end RAM
end LinearProgramming
end Optimization
end OAI
