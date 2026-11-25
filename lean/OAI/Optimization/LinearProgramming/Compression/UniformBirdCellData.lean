import OAI.Optimization.LinearProgramming.Compression.Elimination
import OAI.Optimization.LinearProgramming.RAM.Loops

/-! The data and frame invariants for a dimension-independent Bird entry loop. -/

open scoped BigOperators
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- The indices strictly above the row and strictly before the loop counter. -/
def birdCut {n : ℕ} (i : Fin n) (c : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun k => i < k ∧ k.val < c

@[simp] theorem birdCut_zero {n : ℕ} (i : Fin n) : birdCut i 0 = ∅ := by
  ext k; simp [birdCut]

@[simp] theorem birdCut_end {n : ℕ} (i : Fin n) : birdCut i n = Finset.Ioi i := by
  ext k; simp [birdCut]

theorem birdCut_succ_yes {n c : ℕ} (i : Fin n) (hc : c < n) (h : i.val < c) :
    birdCut i (c+1) = insert ⟨c,hc⟩ (birdCut i c) := by
  ext k
  have := k.isLt
  simp only [birdCut, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.ext_iff, Fin.lt_def]
  omega

theorem birdCut_succ_no {n c : ℕ} (i : Fin n) (h : ¬i.val < c) :
    birdCut i (c+1) = birdCut i c := by
  ext k
  simp only [birdCut, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
  omega

@[simp] theorem notMem_birdCut {n c : ℕ} (i : Fin n) (hc : c < n) :
    (⟨c,hc⟩ : Fin n) ∉ birdCut i c := by simp [birdCut]

/-- Address bank untouched by the inner traversal or its address calculations. -/
def birdCellIndexFrame {K : Type*} (s m : Memory K) : Prop :=
  ∀ p, p ≠ 6 → p ≠ 8 → p ≠ 9 → p ≠ 10 → s.index p = m.index p

theorem birdScalarPut {K : Type*} {P : K → Prop} {m : Memory K} (hm : ∀ p, P (m.data p))
    (dst : ℕ) (v : K) (hv : P v) : ∀ p, P ((m.putData dst v).data p) := by
  intro p
  by_cases heq : p = dst
  · subst p; simpa [Memory.putData] using hv
  · simpa [Memory.putData, Function.update_of_ne heq] using hm p

/-- Scalar code after the input-entry address has been computed. -/
def birdFinishArithmetic : Block :=
  .seq (.op (.load 4 8)) (.seq (.op (.const 6 0)) (.seq (.op (.sub 6 6 1))
    (.seq (.op (.mul 6 6 4)) (.op (.add 6 6 2)))))

theorem birdFinishArithmetic_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (hm : ∀ p, P (m.data p))
    (hzero : P 0) (hneg : P (-m.data 1)) (hprod : P (-m.data 1 * m.data (m.index 8)))
    (hout : P (-m.data 1 * m.data (m.index 8) + m.data 2)) :
    ∃ t, Block.Eval (fun s => ∀ p, P (s.data p)) birdFinishArithmetic m 5 t ∧
      t.data 6 = -m.data 1 * m.data (m.index 8) + m.data 2 ∧
      (∀ p, p ≠ 4 → p ≠ 6 → t.data p = m.data p) ∧ t.index = m.index := by
  let a := m.putData 4 (m.data (m.index 8))
  let b := a.putData 6 (0 : K)
  let c := b.putData 6 (b.data 6 - b.data 1)
  let d := c.putData 6 (c.data 6 * c.data 4)
  let t := d.putData 6 (d.data 6 + d.data 2)
  have ha : ∀ p, P (a.data p) := birdScalarPut hm _ _ (hm _)
  have hb : ∀ p, P (b.data p) := birdScalarPut ha _ _ hzero
  have hc : ∀ p, P (c.data p) := birdScalarPut hb _ _ (by simpa [b,a,Memory.putData] using hneg)
  have hd : ∀ p, P (d.data p) := birdScalarPut hc _ _ (by simpa [c,b,a,Memory.putData] using hprod)
  have ht : ∀ p, P (t.data p) := birdScalarPut hd _ _ (by simpa [d,c,b,a,Memory.putData] using hout)
  have eb : Block.Eval (fun s => ∀ p, P (s.data p)) (.op (.const 6 0)) a 1 b := by
    simpa [b] using Block.Eval.op_const a 6 0 ha (show ∀ p, P ((a.putData 6 ((0:ℚ):K)).data p) by simpa using hb)
  refine ⟨t, .seq (Block.Eval.op_load _ _ _ hm ha) (.seq eb (.seq (Block.Eval.op_sub _ _ _ _ hb hc)
    (.seq (Block.Eval.op_mul _ _ _ _ hc hd) (Block.Eval.op_add _ _ _ _ hd ht)))), ?_, ?_, rfl⟩
  · simp [t,d,c,b,a,Memory.putData]
  · intro p h4 h6; simp [t,d,c,b,a,Memory.putData,Function.update_of_ne h4,Function.update_of_ne h6]

end Compression
end LinearProgramming
end Optimization
end OAI
