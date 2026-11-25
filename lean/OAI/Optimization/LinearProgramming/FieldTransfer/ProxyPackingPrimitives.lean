import OAI.Optimization.LinearProgramming.RAM.Array

/-! The primitive scalar writes used by the symbolic-product operand compactor. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace FieldTransfer
namespace ProxyPacking

open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Write the scalar base and exponent, then advance both output cursors and the pair count. -/
def storePair : Block :=
  .straight [.store 74 20, .store 75 22, .incr 74 74, .incr 75 75, .incr 50 50]

structure Appended (m t : Memory K) (x y : K) : Prop where
  base : t.data (m.index 74) = x
  exponent : t.data (m.index 75) = y
  count : t.index 50 = m.index 50 + 1
  bases : t.index 74 = m.index 74 + 1
  exponents : t.index 75 = m.index 75 + 1
  indexFrame : ∀ j, j ≠ 50 → j ≠ 74 → j ≠ 75 → t.index j = m.index j
  dataFrame : ∀ j, j ≠ 20 → j ≠ 21 → j ≠ 22 →
    j ≠ m.index 74 → j ≠ m.index 75 → t.data j = m.data j

theorem storePair_correct (m : Memory K) {P : K → Prop} (hm : m.AllData P)
    (hb : 128 ≤ m.index 74) (_he : 128 ≤ m.index 75) (hne : m.index 74 ≠ m.index 75) :
    ∃ t, Block.Eval (Memory.AllData P) storePair m 5 t ∧ Appended m t (m.data 20) (m.data 22) := by
  let a := m.putData (m.index 74) (m.data 20)
  let b := a.putData (a.index 75) (a.data 22)
  let c := b.putIndex 74 (b.index 74+1)
  let d := c.putIndex 75 (c.index 75+1)
  let t := d.putIndex 50 (d.index 50+1)
  have ha : a.AllData P := hm.putData _ (hm _)
  have hbb : b.AllData P := ha.putData _ (ha _)
  have ea := Block.Eval.op_store m 74 20 hm ha
  have eb := Block.Eval.op_store a 75 22 ha hbb
  have ec := Block.Eval.op_incr (safe := Memory.AllData P) b 74 74 hbb hbb
  have ed := Block.Eval.op_incr (safe := Memory.AllData P) c 75 75 hbb hbb
  have et := Block.Eval.op_incr (safe := Memory.AllData P) d 50 50 hbb hbb
  refine ⟨t,ea.seq (eb.seq (ec.seq (ed.seq (et.seq (.skip hbb))))),?_⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simp [t,d,c,b,a,hne]
  · simp [t,d,c,b,a,show 22 ≠ m.index 74 by omega]
  · simp [t,d,c,b,a]
  · simp [t,d,c,b,a]
  · simp [t,d,c,b,a]
  · intro j h50 h74 h75
    simp [t,d,c,b,a,h50,h74,h75]
  · intro j _ _ _ h74 h75
    simp [t,d,c,b,a,h74,h75]

/-- A selected row reads its cached magnitude and integer coefficient. The multiplication
by the common denominator occurs in scalar registers before the pair is emitted. -/
def emitRow : Block :=
  .seq (.straight [.load 20 71,.load 21 73,.mul 22 23 21]) storePair

theorem emitRow_correct (m : Memory K) {P : K → Prop} (hm : m.AllData P)
    (hr : 128 ≤ m.index 73) (hb : 128 ≤ m.index 74) (he : 128 ≤ m.index 75)
    (hne : m.index 74 ≠ m.index 75)
    (hp : P (m.data 23 * m.data (m.index 73))) :
    ∃ t, Block.Eval (Memory.AllData P) emitRow m 8 t ∧
      Appended m t (m.data (m.index 71)) (m.data 23 * m.data (m.index 73)) := by
  let a := m.putData 20 (m.data (m.index 71))
  let b := a.putData 21 (a.data (a.index 73))
  let c := b.putData 22 (b.data 23 * b.data 21)
  have ha : a.AllData P := hm.putData _ (hm _)
  have hbb : b.AllData P := ha.putData _ (ha _)
  have hv : b.data 23 * b.data 21 = m.data 23 * m.data (m.index 73) := by
    simp [b,a,show m.index 73 ≠ 20 by omega]
  have hc : c.AllData P := hbb.putData _ (hv ▸ hp)
  have ea := Block.Eval.op_load m 20 71 hm ha
  have eb := Block.Eval.op_load a 21 73 ha hbb
  have ec := Block.Eval.op_mul b 22 23 21 hbb hc
  obtain ⟨t,es,post⟩ := storePair_correct c hc hb he hne
  refine ⟨t,(ea.seq (eb.seq (ec.seq (.skip hc)))).seq es,?_,?_,post.count,post.bases,
    post.exponents,post.indexFrame,?_⟩
  · simpa [c,b,a] using post.base
  · exact post.exponent.trans (by simp [c,hv])
  · intro j h20 h21 h22 h74 h75
    simpa [c,b,a,h20,h21,h22] using post.dataFrame j h20 h21 h22 h74 h75

/-- Advance the magnitude, flag, and coefficient inputs by one position. -/
def advance : Block := .straight [.incr 71 71,.incr 72 72,.incr 73 73]

theorem advance_correct (m : Memory K) {P : K → Prop} (hm : m.AllData P) :
    ∃ t, Block.Eval (Memory.AllData P) advance m 3 t ∧ t.data=m.data ∧
      t.index 71=m.index 71+1 ∧ t.index 72=m.index 72+1 ∧ t.index 73=m.index 73+1 ∧
      ∀ i, i ≠ 71 → i ≠ 72 → i ≠ 73 → t.index i=m.index i := by
  let a := m.putIndex 71 (m.index 71+1)
  let b := a.putIndex 72 (a.index 72+1)
  let t := b.putIndex 73 (b.index 73+1)
  have ea := Block.Eval.op_incr (safe := Memory.AllData P) m 71 71 hm hm
  have eb := Block.Eval.op_incr (safe := Memory.AllData P) a 72 72 hm hm
  have et := Block.Eval.op_incr (safe := Memory.AllData P) b 73 73 hm hm
  refine ⟨t,ea.seq (eb.seq (et.seq (.skip hm))),rfl,?_,?_,?_,?_⟩
  · simp [t,b,a]
  · simp [t,b,a]
  · simp [t,b,a]
  · intro i h71 h72 h73
    simp [t,b,a,h71,h72,h73]

end ProxyPacking
end FieldTransfer
end LinearProgramming
end Optimization
end OAI
