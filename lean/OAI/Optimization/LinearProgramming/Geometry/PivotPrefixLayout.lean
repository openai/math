import OAI.Optimization.LinearProgramming.RAM.ArrayFill

/-! Fixed address-bank bookkeeping for the full pivot prefix. The packed input and row
buffers occupy the scalar bank. The pivot table occupies a disjoint high address-bank region. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace PivotPrefixRAM

open RAM RAM.Block

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Reserve address 128 for the prefix length, 135 and 137 for output/table cursors,
and 139 for the batch status (zero means accepted). -/
def initializePrefix : Block := .straight [.addrConst 128 0, .addrCopy 135 134, .addrCopy 137 136,
  .addrConst 139 0]

def initial (m : Memory K) : Memory K :=
  (((m.putIndex 128 0).putIndex 135 (m.index 134)).putIndex 137 (m.index 136)).putIndex 139 0

/-- The batch protocol uses only the high address registers. The numeric stage reads its
arguments from addresses 0 (column count), 4 (triples), 6 (precision), and 8 (row base). -/
def stageArgs : Block := .straight [.addrCopy 0 130, .addrCopy 4 133, .addrCopy 6 138, .addrCopy 8 135]

def stageMemory (m : Memory K) : Memory K :=
  (((m.putIndex 0 (m.index 130)).putIndex 4 (m.index 133)).putIndex 6 (m.index 138)).putIndex 8 (m.index 135)

/-- Commit the pivot to its table, consume one table cell, increment the prefix length,
and seek to the next output row by a counted scan of its `n` cells. -/
def commitRow : Block := .seq (.straight [.addrStore 137 13, .incr 137 137, .incr 128 128])
  (seekBlock 135 135 10 130)

/-- No scalar arithmetic is performed by the initialization or the address adapter. -/
theorem initialize_eval (m : Memory K) (P : K → Prop) (hs : ∀ i, P (m.data i)) :
    Eval (fun s => ∀ i, P (s.data i)) initializePrefix m 4 (initial m) := by
  let safe := fun s : Memory K => ∀ i, P (s.data i)
  let a := m.putIndex 128 0
  let b := a.putIndex 135 (m.index 134)
  let c := b.putIndex 137 (m.index 136)
  have e1 : Eval safe (.op (.addrConst 128 0)) m 1 a := Eval.op_addrConst _ _ _ hs hs
  have e2 : Eval safe (.op (.addrCopy 135 134)) a 1 b := by
    simpa [a,b] using Eval.op_addrCopy (safe:=safe) a 135 134 hs hs
  have e3 : Eval safe (.op (.addrCopy 137 136)) b 1 c := by
    simpa [a,b,c] using Eval.op_addrCopy (safe:=safe) b 137 136 hs hs
  have e4 : Eval safe (.op (.addrConst 139 0)) c 1 (initial m) := Eval.op_addrConst _ _ _ hs hs
  exact e1.seq (e2.seq (e3.seq (e4.seq (.skip hs))))

theorem stageArgs_eval (m : Memory K) (P : K → Prop) (hs : ∀ i, P (m.data i)) :
    Eval (fun s => ∀ i, P (s.data i)) stageArgs m 4 (stageMemory m) := by
  let safe := fun s : Memory K => ∀ i, P (s.data i)
  let a := m.putIndex 0 (m.index 130)
  let b := a.putIndex 4 (m.index 133)
  let c := b.putIndex 6 (m.index 138)
  have e1 : Eval safe (.op (.addrCopy 0 130)) m 1 a := Eval.op_addrCopy _ _ _ hs hs
  have e2 : Eval safe (.op (.addrCopy 4 133)) a 1 b := by
    simpa [a,b] using Eval.op_addrCopy (safe:=safe) a 4 133 hs hs
  have e3 : Eval safe (.op (.addrCopy 6 138)) b 1 c := by
    simpa [a,b,c] using Eval.op_addrCopy (safe:=safe) b 6 138 hs hs
  have e4 : Eval safe (.op (.addrCopy 8 135)) c 1 (stageMemory m) := by
    simpa [stageMemory,a,b,c] using Eval.op_addrCopy (safe:=safe) c 8 135 hs hs
  exact e1.seq (e2.seq (e3.seq (e4.seq (.skip hs))))

structure Committed (m t : Memory K) : Prop where
  data : t.data=m.data
  row : t.index 128=m.index 128+1
  nextRow : t.index 135=m.index 135+m.index 130
  nextSlot : t.index 137=m.index 137+1
  pivot : t.index (m.index 137)=m.index 13
  frame (i) : i ≠ 10 → i ≠ 128 → i ≠ 135 → i ≠ 137 → i ≠ m.index 137 → t.index i=m.index i

theorem commitRow_spec (m : Memory K) (P : K → Prop) (hs : ∀ i, P (m.data i))
    (high : 256 ≤ m.index 137) :
    ∃ t, Eval (fun s => ∀ i, P (s.data i)) commitRow m (4*m.index 130+6) t ∧ Committed m t := by
  let safe := fun s : Memory K => ∀ i, P (s.data i)
  let a := m.putIndex (m.index 137) (m.index 13)
  let b := a.putIndex 137 (m.index 137+1)
  let c := b.putIndex 128 (m.index 128+1)
  have e1 : Eval safe (.op (.addrStore 137 13)) m 1 a := Eval.op_addrStore _ _ _ hs hs
  have e2 : Eval safe (.op (.incr 137 137)) a 1 b := by
    simpa [a,b,show 137 ≠ m.index 137 by omega] using Eval.op_incr (safe:=safe) a 137 137 hs hs
  have e3 : Eval safe (.op (.incr 128 128)) b 1 c := by
    simpa [a,b,c,show 128 ≠ m.index 137 by omega] using Eval.op_incr (safe:=safe) b 128 128 hs hs
  have count : c.index 130=m.index 130 := by simp [a,b,c,show 130 ≠ m.index 137 by omega]
  obtain ⟨t,seek,hd,_,hp,hf⟩ := seekBlock_correct P c 135 135 10 130 (m.index 130)
    (by decide) (by decide) (by decide) count hs
  refine ⟨t,?_,?_,⟩
  · rw [show 4*m.index 130+6 = 3+(4*m.index 130+3) by omega]
    exact (e1.seq (e2.seq (e3.seq (.skip hs)))).seq seek
  · constructor
    · exact hd
    · simpa [a,b,c] using hf 128 (by decide) (by decide)
    · simpa [a,b,c,show 135 ≠ m.index 137 by omega] using hp
    · simpa [a,b,c] using hf 137 (by decide) (by decide)
    · simpa [a,b,c,show m.index 137 ≠ 137 by omega,show m.index 137 ≠ 128 by omega] using
        hf (m.index 137) (by omega) (by omega)
    · intro i h10 h128 h135 h137 hslot
      simpa [a,b,c,h128,h137,hslot] using hf i h10 h135

end PivotPrefixRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
