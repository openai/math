import OAI.Optimization.LinearProgramming.Geometry.UniformCopy
import OAI.Optimization.LinearProgramming.Geometry.UniformTable

/-! Source and transpose-table callbacks for the uniform Gram projector. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace GramCopy

open RAM
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The source address of an output coordinate, in the caller's initial memory. -/
def tableSource (trans : Bool) (base cols i j : ℕ) : ℕ :=
  base + (if trans then j else i)*cols + (if trans then i else j)

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem source_at (trans : Bool) (start cur : Memory K) {i j : ℕ}
    (hi : cur.index 30 = i) (hj : cur.index 32 = j)
    (hb : cur.index 40 = start.index 40) (hc : cur.index 41 = start.index 41) :
    sourceAddress trans cur = tableSource trans (start.index 40) (start.index 41) i j := by
  cases trans <;> simp [sourceAddress, tableSource, rowRegister, colRegister, hi, hj, hb, hc]

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem keep_tableControl {m t : Memory K} (hf : KeepsAddresses m t)
    (keep : ℕ → Prop) (hk : ∀ p, keep p → p ≠ 38 ∧ p ≠ 39 ∧ p ≠ 42) :
    ∀ p, TableControl p ∨ keep p → t.index p = m.index p := by
  intro p hp
  rcases hp with h | h
  · unfold TableControl at h; rcases h with rfl | rfl | rfl | rfl | rfl <;> exact hf _ (by decide) (by decide) (by decide)
  · rcases hk p h with ⟨ha,hb,hc⟩
    exact hf _ ha hb hc

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem kept_data {t m : Memory K} (care : ℕ → Prop) (h6 : ¬care 6) (x : K)
    (hd : t.data = Function.update m.data 6 x) :
    ∀ p, care p → t.data p = m.data p := by
  intro p hp; rw [hd]
  have hne : p ≠ 6 := fun eq => h6 (eq ▸ hp)
  exact Function.update_of_ne hne _ _

/-- The general table emitter can call this block for either normal or transposed
copy. The source is protected and outside the destination interval. -/
theorem cell_callback (trans : Bool) (P : K → Prop) (care keep : ℕ → Prop)
    (start : Memory K) (rows cols out N : ℕ)
    (hrows : rows ≤ N) (hcols : cols ≤ N) (hstride : start.index 41 ≤ N)
    (h6 : ¬care 6) (hk : ∀ p, keep p → p ≠ 38 ∧ p ≠ 39 ∧ p ≠ 42)
    (h40 : keep 40) (h41 : keep 41)
    (hs : ∀ (i : Fin rows) (j : Fin cols),
      let a := tableSource trans (start.index 40) (start.index 41) i j
      care a ∧ (a < out ∨ out + rows*cols ≤ a)) :
    TableCallbackSpec (cell trans) P care keep start rows cols out
      (fun i j => start.data (tableSource trans (start.index 40) (start.index 41) i j))
      (N*(4*N+5) + 4*N+6) := by
  intro i j m hm hi hj hp hmData
  have hbase := hp _ (Or.inr h40)
  have hstride' := hp _ (Or.inr h41)
  have heq := source_at trans start m hi hj hbase hstride'
  obtain ⟨t,hrun,hd,hf⟩ := cell_spec trans P m hm
  refine ⟨t, _, readCost_le _ _ _ (hi ▸ i.isLt.le.trans hrows) (hj ▸ j.isLt.le.trans hcols)
    (hstride'.trans_le hstride), hrun, ?_, kept_data care h6 _ hd, keep_tableControl hf keep hk⟩
  rw [hd, Function.update_self, heq]
  exact hmData _ (hs i j).1 (hs i j).2

/-- The row-replaced copy feeds the determinant in the cofactor calculation. -/
theorem cofactor_callback (P : K → Prop) (care keep : ℕ → Prop)
    (start : Memory K) (r out : ℕ) (hstride : start.index 41 = r)
    (h0 : P 0) (h1 : P 1) (h6 : ¬care 6) (hk : ∀ p, keep p → p ≠ 38 ∧ p ≠ 39 ∧ p ≠ 42)
    (h40 : keep 40) (h41 : keep 41) (h43 : keep 43) (h44 : keep 44)
    (hs : ∀ (i j : Fin r), let a := start.index 40 + i.val*r + j.val
      care a ∧ (a < out ∨ out + r*r ≤ a)) :
    TableCallbackSpec cofactorCell P care keep start r r out
      (fun i j => if i.val = start.index 43 then (if j.val = start.index 44 then 1 else 0)
        else start.data (start.index 40 + i.val*r + j.val))
      (r*(4*r+5) + 4*r+12) := by
  intro i j m hm hi hj hp hmData
  have hbase := hp _ (Or.inr h40)
  have hstride' := (hp _ (Or.inr h41)).trans hstride
  have heq : sourceAddress false m = start.index 40 + i.val*r + j.val := by
    simp [sourceAddress, rowRegister, colRegister, hi, hj, hbase, hstride']
  obtain ⟨l, hl, t, hrun, hd, hf⟩ := cofactorCell_spec P m hm h0 h1
  refine ⟨t, l, ?_, hrun, ?_, kept_data care h6 _ hd, keep_tableControl hf keep hk⟩
  · have h := readCost_le false m r (hi ▸ i.isLt.le) (hj ▸ j.isLt.le) hstride'.le
    omega
  · rw [hd, Function.update_self]
    simp only [cofactorValue, hi, hj, hp _ (Or.inr h43), hp _ (Or.inr h44), heq,
      hmData _ (hs i j).1 (hs i j).2]

end GramCopy
end Geometry
end LinearProgramming
end Optimization
end OAI
