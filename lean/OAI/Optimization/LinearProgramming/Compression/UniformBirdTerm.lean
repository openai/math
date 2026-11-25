import OAI.Optimization.LinearProgramming.Compression.UniformIndex

/-! A single eligible summation index in Bird's division-free determinant recurrence. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
open RAM

private def readBirdCell (dst base row col : ℕ) : Block :=
  .seq (cellAddress 8 9 10 base 0 row col) (.op (.load dst 8))

private def keepsBirdIndex {K : Type} (m t : Memory K) : Prop :=
  ∀ p, p ≠ 8 → p ≠ 9 → p ≠ 10 → t.index p = m.index p

private theorem keepsBirdIndex.trans {K : Type} {m s t : Memory K}
    (h : keepsBirdIndex m s) (g : keepsBirdIndex s t) : keepsBirdIndex m t :=
  fun p h8 h9 h10 => (g p h8 h9 h10).trans (h p h8 h9 h10)

private theorem keepsBirdIndex.small {K : Type} {m s : Memory K} (h : keepsBirdIndex m s)
    (p : ℕ) (hp : p < 8) : s.index p = m.index p := h p (by omega) (by omega) (by omega)

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem birdSafeWrite {P : K → Prop} {m : Memory K}
    (hm : ∀ p, P (m.data p)) (d : ℕ) {v : K} (hv : P v) : ∀ p, P ((m.putData d v).data p) := by
  intro p; by_cases h : p = d <;> simp [Memory.putData, h, hm, hv]

private theorem readBirdCell_spec (P : K → Prop) (m : Memory K) (hm : ∀ p, P (m.data p))
    (dst base row col : ℕ) (hrow : row < 8) (hcol : col < 8)
    (hr : m.index row < m.index 0) (hc : m.index col < m.index 0) :
    ∃ cost t, cost ≤ 20*(m.index 0+1)^2 ∧
      Block.Eval (fun z => ∀ p, P (z.data p)) (readBirdCell dst base row col) m cost t ∧
      t.data = Function.update m.data dst (m.data (m.index base + m.index row*m.index 0 + m.index col)) ∧
      keepsBirdIndex m t := by
  have hs : CellScratchOK 8 9 10 0 row col := by
    refine ⟨by decide, by decide, by decide, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> omega
  obtain ⟨v, ev, hd, indices, ha⟩ :=
    cellAddress_spec (fun f => ∀ p, P (f p)) m hm 8 9 10 base 0 row col hs
  let t := v.putData dst (v.data (v.index 8))
  have hv : ∀ p, P (v.data p) := ev.safe_end
  have e : Block.Eval (fun z => ∀ p, P (z.data p)) (.op (.load dst 8)) v 1 t :=
    Block.Eval.op_load _ _ _ hv (birdSafeWrite hv _ (hv _))
  refine ⟨_, t, ?_, ev.seq e, ?_, indices⟩
  · calc
      _ ≤ m.index 0*(4*m.index 0+5) + 4*m.index 0 + 5 + 1 := by gcongr
      _ ≤ _ := by nlinarith
  · simp [t, Memory.putData, hd, ha]

/-- Adds the diagonal and dot-product contributions at an eligible `k`. Matrix
cells and the loop indices survive the three row-major lookups. -/
def uniformBirdTerm : Block :=
  .seq (readBirdCell 5 2 6 6) (.seq (readBirdCell 3 2 4 6) (.seq (readBirdCell 4 1 6 5)
    (.seq (.op (.add 1 1 5)) (.seq (.op (.mul 5 3 4)) (.op (.add 2 2 5))))))

theorem uniformBirdTerm_spec (m : Memory K) (P : K → Prop) (hm : ∀ p, P (m.data p))
    (hi : m.index 4 < m.index 0) (hj : m.index 5 < m.index 0) (hk : m.index 6 < m.index 0)
    (hinput : 7 ≤ m.index 1) (hprevious : 7 ≤ m.index 2)
    (hdiag : P (m.data 1 + m.data (m.index 2 + m.index 6*m.index 0 + m.index 6)))
    (hprod : P (m.data (m.index 2 + m.index 4*m.index 0 + m.index 6) *
                m.data (m.index 1 + m.index 6*m.index 0 + m.index 5)))
    (hdot : P (m.data 2 + m.data (m.index 2 + m.index 4*m.index 0 + m.index 6) *
                m.data (m.index 1 + m.index 6*m.index 0 + m.index 5))) :
    ∃ cost t, cost ≤ 100*(m.index 0+1)^2 ∧
      Block.Eval (fun s => ∀ p, P (s.data p)) uniformBirdTerm m cost t ∧
      t.data 1 = m.data 1 + m.data (m.index 2 + m.index 6*m.index 0 + m.index 6) ∧
      t.data 2 = m.data 2 + m.data (m.index 2 + m.index 4*m.index 0 + m.index 6) *
                       m.data (m.index 1 + m.index 6*m.index 0 + m.index 5) ∧
      (∀ p, 7 ≤ p → t.data p = m.data p) ∧
      (∀ p, p ≠ 8 → p ≠ 9 → p ≠ 10 → t.index p = m.index p) := by
  let fkk := m.data (m.index 2 + m.index 6*m.index 0 + m.index 6)
  let fik := m.data (m.index 2 + m.index 4*m.index 0 + m.index 6)
  let akj := m.data (m.index 1 + m.index 6*m.index 0 + m.index 5)
  obtain ⟨c1,v1,hc1,e1,d1,i1⟩ := readBirdCell_spec P m hm 5 2 6 6 (by decide) (by decide) hk hk
  change v1.data = Function.update m.data 5 fkk at d1
  obtain ⟨c2,v2,hc2,e2,d2,i2⟩ := readBirdCell_spec P v1 e1.safe_end 3 2 4 6
    (by decide) (by decide)
    (by simpa only [i1.small 4 (by decide), i1.small 0 (by decide)] using hi)
    (by simpa only [i1.small 6 (by decide), i1.small 0 (by decide)] using hk)
  have i02 := i1.trans i2
  have large1 (p : ℕ) (hp : 7 ≤ p) : v1.data p = m.data p := by
    rw [d1, Function.update_of_ne (by omega : p ≠ 5)]
  rw [i1.small 2 (by decide), i1.small 4 (by decide), i1.small 0 (by decide),
    i1.small 6 (by decide), large1 _ (by omega)] at d2
  change v2.data = Function.update v1.data 3 fik at d2
  have large2 (p : ℕ) (hp : 7 ≤ p) : v2.data p = m.data p := by
    rw [d2, Function.update_of_ne (by omega : p ≠ 3), large1 p hp]
  obtain ⟨c3,v3,hc3,e3,d3,i3⟩ := readBirdCell_spec P v2 e2.safe_end 4 1 6 5
    (by decide) (by decide)
    (by simpa only [i02.small 6 (by decide), i02.small 0 (by decide)] using hk)
    (by simpa only [i02.small 5 (by decide), i02.small 0 (by decide)] using hj)
  rw [i02.small 1 (by decide), i02.small 6 (by decide), i02.small 0 (by decide),
    i02.small 5 (by decide), large2 _ (by omega)] at d3
  change v3.data = Function.update v2.data 4 akj at d3
  let t4 := v3.putData 1 (v3.data 1 + v3.data 5)
  let t5 := t4.putData 5 (t4.data 3 * t4.data 4)
  let t6 := t5.putData 2 (t5.data 2 + t5.data 5)
  have diag : v3.data 1 + v3.data 5 = m.data 1 + fkk := by simp [d3,d2,d1]
  have mult : t4.data 3 * t4.data 4 = fik*akj := by simp [t4,Memory.putData,d3,d2,d1]
  have dot : t5.data 2 + t5.data 5 = m.data 2 + fik*akj := by
    simp [t5,t4,Memory.putData,d3,d2,d1]
  have e4 : Block.Eval (fun z => ∀ p, P (z.data p)) (.op (.add 1 1 5)) v3 1 t4 :=
    Block.Eval.op_add _ _ _ _ e3.safe_end (birdSafeWrite e3.safe_end _ (diag ▸ hdiag))
  have e5 : Block.Eval (fun z => ∀ p, P (z.data p)) (.op (.mul 5 3 4)) t4 1 t5 :=
    Block.Eval.op_mul _ _ _ _ e4.safe_end (birdSafeWrite e4.safe_end _ (mult ▸ hprod))
  have e6 : Block.Eval (fun z => ∀ p, P (z.data p)) (.op (.add 2 2 5)) t5 1 t6 :=
    Block.Eval.op_add _ _ _ _ e5.safe_end (birdSafeWrite e5.safe_end _ (dot ▸ hdot))
  refine ⟨_,t6, ?_, e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6)))), ?_, ?_, ?_, i02.trans i3⟩
  · rw [i1.small 0 (by decide)] at hc2
    rw [i02.small 0 (by decide)] at hc3
    nlinarith
  · simpa [t6,t5,t4,Memory.putData,Function.update_apply] using diag
  · simpa [t6,Memory.putData,Function.update_apply] using dot
  · intro p hp
    have h1 : p ≠ 1 := by omega
    have h2 : p ≠ 2 := by omega
    have h3 : p ≠ 3 := by omega
    have h4 : p ≠ 4 := by omega
    have h5 : p ≠ 5 := by omega
    simp [t6,t5,t4,Memory.putData,h1,h2,h3,h4,h5,d3,d2,d1]

end Compression
end LinearProgramming
end Optimization
end OAI
