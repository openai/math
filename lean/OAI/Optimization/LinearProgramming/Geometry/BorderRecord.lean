import OAI.Optimization.LinearProgramming.Geometry.BorderLayout
import OAI.Optimization.LinearProgramming.Geometry.BorderWords
import OAI.Optimization.LinearProgramming.Geometry.BorderColumns

/-! One fully written descriptor and the ordered selector it references. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM Compression.MinorLoad Matrix

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {r n k : ℕ}

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem Layout.Ready.of_frame {L : Layout r n} {D : Matrix (Fin r) (Fin n) K} {J : Fin k → Fin n}
    {m t : Memory K} (h : L.Ready D J m) (hr : k+1 ≤ r) (hd : t.data=m.data)
    (frame : ∀ p, 128 ≤ p → p < L.headers → t.index p=m.index p) : L.Ready D J t := by
  have hg := L.pivots_ge
  have he := L.pivots_end
  have ctrl (p : ℕ) (hp : 128 ≤ p) (hp' : p ≤ 145) := frame p hp (by omega)
  refine ⟨(ctrl _ (by decide) (by decide)).trans h.prefixCount, (ctrl _ (by decide) (by decide)).trans h.height,
    (ctrl _ (by decide) (by decide)).trans h.width, (ctrl _ (by decide) (by decide)).trans h.sourceAddr,
    (ctrl _ (by decide) (by decide)).trans h.priceAddr, (ctrl _ (by decide) (by decide)).trans h.tripleAddr,
    (ctrl _ (by decide) (by decide)).trans h.roundedAddr, (ctrl _ (by decide) (by decide)).trans h.pivotAddr,
    (ctrl _ (by decide) (by decide)).trans h.headerAddr, (ctrl _ (by decide) (by decide)).trans h.rowAddr,
    (ctrl _ (by decide) (by decide)).trans h.colAddr, (ctrl _ (by decide) (by decide)).trans h.answerAddr,
    (ctrl _ (by decide) (by decide)).trans h.scratchAddr, (ctrl _ (by decide) (by decide)).trans h.maskAddr,
    ?_, ?_⟩
  · intro i
    rw [frame _ (by omega) (by have := i.isLt; omega), h.pivotData]
  · intro i j
    rw [hd, h.matrixData]

def emitRecord : Block := .seq emitHeader emitColumn

structure RecordEnd (L : Layout r n) (D : Matrix (Fin r) (Fin n) K) (hr : k+1 ≤ r)
    (J : Fin k → Fin n) (a : Fin n) (s t : Memory K) : Prop where
  data : t.data=s.data
  outer : t.index 0=a.val
  minorSize : t.index 7=k+1
  headerCursor : t.index 3=L.headers+6*(a.val+1)
  columnCursor : t.index 4=L.cols+(k+1)*(a.val+1)
  words : ∀ w<6, t.index (L.headers+6*a.val+w)=descriptorWord ((L.batch D hr J).query a) w
  selector : ∀ i : Fin (k+1), t.index (L.cols+(k+1)*a.val+i.val)=(Fin.lastCases (motive := fun _ => Fin n) a J i).val
  frame : ∀ p, 8 ≤ p → (p < L.headers+6*a.val ∨ L.headers+6*a.val+6 ≤ p) →
    (p < L.cols+(k+1)*a.val ∨ L.cols+(k+1)*a.val+k+1 ≤ p) → t.index p=s.index p

/-- Write the next request record and selector; the two cursors stream forward without
multiplication inside the runtime loop. -/
theorem emitRecord_spec (P : K → Prop) (s : Memory K) (hs : s.AllData P)
    (L : Layout r n) (D : Matrix (Fin r) (Fin n) K) (hr : k+1 ≤ r) (J : Fin k → Fin n)
    (a : Fin n) (ready : L.Ready D J s) (h0 : s.index 0=a.val) (h7 : s.index 7=k+1)
    (h3 : s.index 3=L.headers+6*a.val) (h4 : s.index 4=L.cols+(k+1)*a.val) :
    ∃ t, Block.Eval (Memory.AllData P) emitRecord s (k*7+19) t ∧ RecordEnd L D hr J a s t := by
  have hp := L.pivots_ge
  have hp' := L.pivots_end
  have hhbase := L.headers_end
  have hrbase := L.rows_end
  have ha := a.isLt
  have hsep : s.index 3+6 ≤ L.cols+(k+1)*a.val := by
    have hsix := Nat.mul_le_mul_left 6 (Nat.succ_le_of_lt ha)
    rw [Nat.mul_succ] at hsix
    omega
  obtain ⟨u, he, headEnd⟩ := emitHeader_spec P s hs (by omega)
  have low (b : ℕ) (h : b<256) (h' : b≠3) := headEnd.frame b h' (Or.inl (by omega))
  obtain ⟨t, ce, colEnd⟩ := emitColumn_spec P u he.safe_end a.val k L.pivots (L.cols+(k+1)*a.val)
    ((low 0 (by decide) (by decide)).trans h0) ((low 128 (by decide) (by decide)).trans ready.prefixCount)
    ((low 136 (by decide) (by decide)).trans ready.pivotAddr) ((low 4 (by decide) (by decide)).trans h4)
    hp (by omega)
  have hfront (p : ℕ) (hp' : p < L.cols+(k+1)*a.val) (h1 : p≠1) (h4 : p≠4) (h5 : p≠5) (h6 : p≠6) (h7 : p≠7) :=
    colEnd.frame p h1 h4 h5 h6 h7 (Or.inl hp')
  refine ⟨t, ?_, colEnd.data.trans headEnd.data,
    (hfront 0 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((low 0 (by decide) (by decide)).trans h0), colEnd.prefixSize, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [emitRecord, show 12 + (k*7+7) = k*7+19 by omega] using he.seq ce
  · rw [hfront 3 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide),headEnd.cursor,h3]
    ring
  · rw [colEnd.cursor]; ring
  · intro w hw
    have hw' := headEnd.words ⟨w, hw⟩
    rw [h3] at hw'
    rw [hfront _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), hw']
    interval_cases w <;> simp [Layout.batch, descriptorWord, ready.sourceAddr, ready.width, ready.rowAddr,
      ready.scratchAddr, h4,h7]
  · intro i
    refine Fin.lastCases ?_ (fun b => ?_) i
    · simpa only [Fin.val_last, Fin.lastCases_last] using colEnd.appendWord
    · have hw := colEnd.prefixWord b.val b.isLt
      have hread := headEnd.frame (L.pivots+b.val) (by omega) (Or.inl (by have := b.isLt; omega))
      simpa only [Fin.val_castSucc, Fin.lastCases_castSucc] using hw.trans (hread.trans (ready.pivotData b))
  · intro p h8 hhead hcols
    rw [colEnd.frame p (by omega) (by omega) (by omega) (by omega) (by omega) hcols,
      headEnd.frame p (by omega) (h3 ▸ hhead)]

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
