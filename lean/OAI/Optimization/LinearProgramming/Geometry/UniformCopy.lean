import OAI.Optimization.LinearProgramming.Compression.UniformIndex

/-! Uniform source-cell, transpose, and cofactor-copy callbacks for the Gram matrix
RAM. Data register 6 receives the output. The two dimension/position registers 30
and 32 and source metadata registers 40, 41 are never overwritten. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace GramCopy

open RAM Compression

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def rowRegister (transpose : Bool) : ℕ := if transpose then 32 else 30
def colRegister (transpose : Bool) : ℕ := if transpose then 30 else 32

def cell (transpose : Bool) : Block :=
  .seq (cellAddress 38 39 42 40 41 (rowRegister transpose) (colRegister transpose))
    (.op (.load 6 38))

def sourceAddress (transpose : Bool) (m : Memory K) : ℕ :=
  m.index 40 + m.index (rowRegister transpose) * m.index 41 + m.index (colRegister transpose)

def readCost (transpose : Bool) (m : Memory K) : ℕ :=
  m.index (rowRegister transpose) * (4*m.index 41+5) + 4*m.index (colRegister transpose)+6

def KeepsAddresses (m t : Memory K) : Prop :=
  ∀ p, p ≠ 38 → p ≠ 39 → p ≠ 42 → t.index p = m.index p

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem safe_write (m : Memory K) (P : K → Prop) (h : ∀ i, P (m.data i))
    (v : K) (hv : P v) : ∀ i, P ((m.putData 6 v).data i) := by
  intro i
  by_cases hi : i = 6 <;> simp [Memory.putData, hi, hv, h]

/-- Each callback is a single fixed RAM block for all source dimensions. Its exact
step count includes all indexing arithmetic and its only scalar write. -/
theorem cell_spec (transpose : Bool) (P : K → Prop) (m : Memory K)
    (hm : ∀ p, P (m.data p)) :
    ∃ t, Block.Eval (fun w => ∀ p, P (w.data p)) (cell transpose) m (readCost transpose m) t ∧
      t.data = Function.update m.data 6 (m.data (sourceAddress transpose m)) ∧ KeepsAddresses m t := by
  have hs : CellScratchOK 38 39 42 41 (rowRegister transpose) (colRegister transpose) := by
    cases transpose <;> simp [CellScratchOK, rowRegister, colRegister]
  obtain ⟨u, he, hd, hf, ha⟩ := cellAddress_spec (fun f => ∀ p, P (f p)) m hm
      38 39 42 40 41 (rowRegister transpose) (colRegister transpose) hs
  let t := u.putData 6 (u.data (u.index 38))
  have hread : Block.Eval (fun w => ∀ p, P (w.data p)) (.op (.load 6 38)) u 1 t :=
    Block.Eval.op_load _ _ _ he.safe_end (safe_write _ P he.safe_end _ (he.safe_end _))
  exact ⟨t, by simpa [cell, readCost, Nat.add_assoc] using he.seq hread,
    by simp [t, Memory.putData, hd, ha, sourceAddress], hf⟩

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
/-- An assignment `target[i,j] := source[i,j]` (`transpose=false`) or its transpose
(`transpose=true`). Inputs bound both source dimensions by `N`. -/
theorem readCost_le (transpose : Bool) (m : Memory K) (N : ℕ)
    (hr : m.index 30 ≤ N) (hc : m.index 32 ≤ N) (hd : m.index 41 ≤ N) :
    readCost transpose m ≤ N*(4*N+5) + 4*N+6 := by
  cases transpose <;> simp only [readCost, rowRegister, colRegister, Bool.false_eq_true,
    ↓reduceIte] <;> gcongr

/-- Comparison of two addresses, compiled with the two available less-than branches. -/
def ifAddressEq (i j : ℕ) (yes no : Block) : Block :=
  .branch (.addrLT i j) no (.branch (.addrLT j i) no yes)

theorem eval_ifAddressEq {safe : Memory K → Prop} (i j : ℕ) (yes no : Block)
    (m t : Memory K) (k : ℕ)
    (h : Block.Eval safe (if m.index i = m.index j then yes else no) m k t) :
    ∃ l ≤ k + 3, Block.Eval safe (ifAddressEq i j yes no) m l t := by
  by_cases he : m.index i = m.index j
  · simp only [he, ite_true] at h
    have hf : (Cond.addrLT i j).test m = false := by simp [Cond.test, he]
    have hf' : (Cond.addrLT j i).test m = false := by simp [Cond.test, he]
    exact ⟨_, by omega, Block.Eval.branchFalse hf (Block.Eval.branchFalse hf' h)⟩
  · simp only [he, ite_false] at h
    rcases lt_or_gt_of_ne he with lt | gt
    · have hc : (Cond.addrLT i j).test m = true := by simp [Cond.test, lt]
      exact ⟨_, by omega, Block.Eval.branchTrue hc h⟩
    · have hc : (Cond.addrLT i j).test m = false := by simp [Cond.test, gt.not_gt]
      have hc' : (Cond.addrLT j i).test m = true := by simp [Cond.test, gt]
      exact ⟨_, by omega, Block.Eval.branchFalse hc (Block.Eval.branchTrue hc' h)⟩

/-- Form a row-replaced cofactor. Address 43 is the row to replace, and address
44 names the coordinate which receives one in the replacement row. -/
def cofactorCell : Block :=
  ifAddressEq 30 43 (ifAddressEq 32 44 (.op (.const 6 1)) (.op (.const 6 0))) (cell false)

def cofactorValue (m : Memory K) : K :=
  if m.index 30 = m.index 43 then (if m.index 32 = m.index 44 then 1 else 0)
  else m.data (sourceAddress false m)

theorem cofactorCell_spec (P : K → Prop) (m : Memory K) (hm : ∀ p, P (m.data p))
    (h0 : P 0) (h1 : P 1) :
    ∃ l ≤ readCost false m + 6, ∃ t,
      Block.Eval (fun w => ∀ p, P (w.data p)) cofactorCell m l t ∧
      t.data = Function.update m.data 6 (cofactorValue m) ∧ KeepsAddresses m t := by
  by_cases row : m.index 30 = m.index 43
  · let bit : K := if m.index 32 = m.index 44 then 1 else 0
    let t := m.putData 6 bit
    have hc : Block.Eval (fun w => ∀ p, P (w.data p))
        (if m.index 32 = m.index 44 then .op (.const 6 1) else .op (.const 6 0)) m 1 t := by
      by_cases col : m.index 32 = m.index 44
      · simp only [col, ite_true, t, bit]
        simpa using Block.Eval.op_const m 6 1 hm (by simpa using safe_write m P hm 1 h1)
      · simp only [col, ite_false, t, bit]
        simpa using Block.Eval.op_const m 6 0 hm (by simpa using safe_write m P hm 0 h0)
    obtain ⟨z, hz, hzrun⟩ := eval_ifAddressEq 32 44 _ _ m t 1 hc
    obtain ⟨l, hl, hrun⟩ := eval_ifAddressEq 30 43 _ (cell false) m t z (by simpa [row] using hzrun)
    refine ⟨l, ?_, t, hrun, by simp [cofactorValue, t, bit, Memory.putData, row], ?_⟩
    · unfold readCost; omega
    · exact fun _ _ _ _ => rfl
  · obtain ⟨t, he, hd, hf⟩ := cell_spec false P m hm
    obtain ⟨l, hl, hrun⟩ := eval_ifAddressEq 30 43
      (ifAddressEq 32 44 (.op (.const 6 1)) (.op (.const 6 0))) (cell false) m t _
      (by simpa [row] using he)
    exact ⟨l, by omega, t, hrun, by simpa [cofactorValue, row] using hd, hf⟩

end GramCopy
end Geometry
end LinearProgramming
end Optimization
end OAI
