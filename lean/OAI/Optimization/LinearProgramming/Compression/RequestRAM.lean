import OAI.Optimization.LinearProgramming.Compression.RequestBasis
import OAI.Optimization.LinearProgramming.Compression.ProjectionAffineHeight
import OAI.Optimization.LinearProgramming.RAM.Array

/-! A fixed scalar RAM block inspects one contiguous row of a reduced graph basis.
Both readers in the norm computation point to the same row. The second-to-last cell
is the integer coefficient at the requested coordinate. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestScreen

open RAM RAM.Dense
open scoped BigOperators

private def flag (b : ℕ) : Block := .op (.addrConst 25 b)

private def classify : Block :=
  .branch (.scalarLT 0 20) (flag 0)
    (.branch (.scalarLT 1 2) (flag 1) (.branch (.scalarLT 2 1) (flag 1) (flag 0)))

private theorem classify_spec (P : ℚ → Prop) (m : Memory ℚ) (hm : m.AllData P)
    (hzero : m.data 2 = 0) :
    ∃ k ≤ 5, ∃ b : ℕ, Block.Eval (Memory.AllData P) classify m k (m.putIndex 25 b) ∧
      (b = 1 ↔ m.data 1 ≠ 0 ∧ m.data 20 ≤ m.data 0) ∧ (b = 1 ∨ b = 0) := by
  have setflag (b : ℕ) : Block.Eval (Memory.AllData P) (flag b) m 1 (m.putIndex 25 b) :=
    Block.Eval.op_addrConst m 25 b hm (hm.putIndex 25 b)
  by_cases hcut : m.data 0 < m.data 20
  · refine ⟨3, by decide, 0, .branchTrue (by simpa [Cond.test] using hcut) (setflag 0), ?_, Or.inr rfl⟩
    simp [not_le_of_gt hcut]
  · have hgood := le_of_not_gt hcut
    have hct : (Cond.scalarLT 0 20).test m = false := by simp [Cond.test, hcut]
    by_cases hneg : m.data 1 < 0
    · refine ⟨4, by decide, 1, .branchFalse hct (.branchTrue (by simp [Cond.test, hzero, hneg]) (setflag 1)),
        ?_, Or.inl rfl⟩
      simp [hneg.ne, hgood]
    · have hcneg : (Cond.scalarLT 1 2).test m = false := by simp [Cond.test, hzero, hneg]
      by_cases hpos : 0 < m.data 1
      · refine ⟨5, le_rfl, 1, .branchFalse hct (.branchFalse hcneg
          (.branchTrue (by simp [Cond.test, hzero, hpos]) (setflag 1))), ?_, Or.inl rfl⟩
        simp [hpos.ne', hgood]
      · refine ⟨4, by decide, 0, .branchFalse hct (.branchFalse hcneg
          (.branchFalse (by simp [Cond.test, hzero, hpos]) (setflag 0))), ?_, Or.inr rfl⟩
        simp [le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)]

/-- Output is a binary acceptance flag in address register 25. -/
def block : Block :=
  .seq dotBlock (.seq (.op (.decr 24 20)) (.seq (.op (.decr 24 24))
    (.seq (.op (.load 1 24)) classify)))

private theorem square_dot {d : ℕ} (w : Fin d → ℚ) (z : Fin d → ℤ) :
    dotProduct (requestGraphRat w z) (requestGraphRat w z) = requestGraphSquare w z := by
  rw [dotProduct, Fin.sum_univ_castSucc]
  simp [requestGraphSquare, pow_two]

/-- For any rational graph basis row, `block` implements the exact predicate used by
`requestCandidate`. The dimension-independent program takes at most `9*(n+2)+11`
instructions and preserves the bit bound at every step. -/
theorem block_spec {n B : ℕ} (w : Fin (n+1) → ℚ) (z : Fin (n+1) → ℤ) (m : Memory ℚ)
    (hheight : ∀ j, ((requestGraphRat w z) j).num.natAbs ≤ B ∧ ((requestGraphRat w z) j).den ≤ B)
    (hsafe : m.AllData (fun a => ratBits a ≤ affineEvalBits (n+2) B))
    (haddr : 23 < m.index 20) (hmirror : m.index 21 = m.index 20) (hwidth : m.index 23 = n+2)
    (hrow : ∀ j : Fin (n+2), m.data (m.index 20+j.val) = requestGraphRat w z j)
    (hcap : m.data 0 = (requestCutoff (n+1) : ℚ)^2) (hzero : m.data 2 = 0) :
    ∃ k ≤ 9*(n+2)+11, ∃ t, Block.Eval (Memory.AllData (fun a => ratBits a ≤ affineEvalBits (n+2) B))
      block m k t ∧ (t.index 25 = 1 ↔ z (Fin.last n) ≠ 0 ∧
        requestGraphSquare w z ≤ (requestCutoff (n+1) : ℚ)^2) ∧ (t.index 25 = 1 ∨ t.index 25 = 0) ∧
      t.index 20 = m.index 20 + (n+2) ∧ t.index 21 = t.index 20 ∧
      (∀ j, j < 20 ∨ 22 < j → j ≠ 24 → j ≠ 25 → t.index j = m.index j) ∧
      (∀ j, j < 20 ∨ 23 < j → j ≠ 1 → t.data j = m.data j) := by
  let P : ℚ → Prop := fun a => ratBits a ≤ affineEvalBits (n+2) B
  let x := fun i => m.data (m.index 20+i)
  have hx (i : ℕ) (hi : i < n+2) : (x i).num.natAbs ≤ B ∧ (x i).den ≤ B := by
    simpa only [x, hrow ⟨i, hi⟩] using hheight ⟨i, hi⟩
  have hB : 1 ≤ B := ((requestGraphRat w z (Fin.last (n+1))).den_pos).trans_le (hheight _).2
  have hterm (j : ℕ) (hj : j < n+2) : P (dotTerm m j) := by
    change ratBits _ ≤ _
    simpa [dotTerm, hmirror, x] using
      (ratBits_affine_product (x j) (x j) (hx j hj) (hx j hj)).trans (affineEvalBits_mono (Nat.zero_le (n+2)))
  have hsum (j : ℕ) (hj : j ≤ n+2) : P (dotPrefix m j) := by
    have hh (i : ℕ) (hi : i ∈ Finset.range j) := hx i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj)
    have hs := ratBits_affine_partial_sum (Finset.range j) x x 0 hB (by simp [hB]) hh hh
    simpa [P, dotPrefix, dotTerm, hmirror, x] using hs.trans
      (affineEvalBits_mono (B := B) (by simpa using hj : (Finset.range j).card ≤ n+2))
  obtain ⟨a, run, ha⟩ := dotBlock_correct P m (n+2) hsafe haddr (hmirror ▸ haddr) hwidth hterm hsum
  have hcalc : a.data 20 = requestGraphSquare w z := by
    rw [ha.sum, ← square_dot, dotPrefix, dotProduct, Finset.sum_range]
    exact Finset.sum_congr rfl fun j _ => by simp [dotTerm, hmirror, hrow j]
  let s₁ := a.putIndex 24 (a.index 20 - 1)
  let s₂ := s₁.putIndex 24 (s₁.index 24 - 1)
  let t := s₂.putData 1 (s₂.data (s₂.index 24))
  have h₁ : Block.Eval (Memory.AllData P) (.op (.decr 24 20)) a 1 s₁ :=
    .op run.safe_end (run.safe_end.putIndex 24 _) (fun _ => rfl)
  have h₂ : Block.Eval (Memory.AllData P) (.op (.decr 24 24)) s₁ 1 s₂ :=
    .op h₁.safe_end (h₁.safe_end.putIndex 24 _) (fun _ => rfl)
  have h₃ : Block.Eval (Memory.AllData P) (.op (.load 1 24)) s₂ 1 t :=
    .op_load _ _ _ h₂.safe_end (h₂.safe_end.putData 1 (h₂.safe_end _))
  have hptr : s₂.index 24 = m.index 20+n := by
    simp [s₂, s₁, ha.left]
  have hcell : t.data 1 = z (Fin.last n) := by
    have jf : 23 < m.index 20+n := by omega
    simp only [t, Memory.putData_same, hptr, s₂, s₁, Memory.putIndex_data, ha.dataFrame _ (Or.inr jf)]
    simpa using hrow (Fin.last n).castSucc
  have ht0 : t.data 0 = (requestCutoff (n+1) : ℚ)^2 := by
    simpa [t, s₂, s₁, Memory.putData, ha.dataFrame 0 (by decide)] using hcap
  have ht2 : t.data 2 = 0 := by
    simpa [t, s₂, s₁, Memory.putData, ha.dataFrame 2 (by decide)] using hzero
  have ht20 : t.data 20 = requestGraphSquare w z := by
    simpa [t, s₂, s₁, Memory.putData] using hcalc
  obtain ⟨aCost, hcost, b, hclass, hcriterion, hbinary⟩ := classify_spec P t h₃.safe_end ht2
  refine ⟨_, by omega, _, Block.Eval.seq run (.seq h₁ (.seq h₂ (.seq h₃ hclass))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hcell, ht0, ht20] using hcriterion
  · simpa using hbinary
  · simp [t, s₂, s₁, Memory.putIndex, ha.left]
  · simp [t, s₂, s₁, Memory.putIndex, ha.left, ha.right, hmirror]

  · intro j hj h24 h25
    simp [t, s₂, s₁, Memory.putIndex, Function.update_of_ne h24, Function.update_of_ne h25, ha.indexFrame j hj]
  · intro j hj h1
    simp [t, s₂, s₁, Memory.putData, Function.update_of_ne h1, ha.dataFrame j hj]

end RequestScreen
end Compression
end LinearProgramming
end Optimization
end OAI
