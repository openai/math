import OAI.Optimization.LinearProgramming.Compression.ServiceState
import OAI.Optimization.LinearProgramming.Compression.ServiceTableInsert

/-! The persistent minor service after insertion of the staged generator at a restart. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM GeneratorTable

variable {d e n : ℕ} {D : Matrix (Fin d) (Fin n) ℚ} {E : Matrix (Fin e) (Fin n) ℚ}

/-- The native table update preserves the two matrices, their dimensions, all scalar
height bounds and the high return-address bank, and publishes the exact larger generator
set in canonical order. `staged` is the record prepared from the actual requested minor. -/
theorem Persistent.commitGenerator {J : Finset (NonzeroPairMinor D E)} {H : ℕ} {s : Memory ℚ}
    (h : Persistent D E J H s) (q : NonzeroPairMinor D E) (fresh : q ∉ J)
    (staged : SlotAt D E q (slotBase n (J.card+1)) s)
    (h14 : s.index 14=tableBase n) (h18 : s.index 18=stride n) (h19 : s.index 19=rank q J.sort)
    (h20 : s.index 20=slotBase n J.card) (h21 : s.index 21=slotBase n (J.card+1))
    (hone : ratBits (1:ℚ)≤H) (hcount : ratBits ((J.card+1:ℕ):ℚ)≤H) :
    ∃ t c, c ≤ 30*(J.card+1)*(stride n+1) ∧
      Block.Eval (Memory.AllData (fun z => ratBits z≤H)) insertAtRank s c t ∧
      Persistent D E (insert q J) H t ∧ (∀ a, 40≤a → t.index a=s.index a) ∧
      ∀ a, a≠0 → a≠4 → a<tableBase n → t.data a=s.data a := by
  have freshList : q ∉ J.sort := by simpa using fresh
  obtain ⟨t,run,newTable,addresses,frame⟩ := insertAtRank_spec D E J.sort q (fun z => ratBits z≤H) s
    h.generators (by simpa using staged) freshList h14 h18 h19 (by simpa using h20) (by simpa using h21)
    h.bounds hone (by simpa using hcount)
  have cost := insertCost_le n J.sort.length (rank q J.sort) (rank_le_length q J.sort)
  have tbl : Stored D E (insert q J).sort t := by
    simpa using h.generators.canonical_inserted freshList newTable
  have low (a : ℕ) (ha : a≤3) : a<tableBase n := by unfold tableBase; omega
  refine ⟨t,_,by simpa using cost,run,?_,addresses,frame⟩
  refine ⟨(frame 1 (by decide) (by decide) (low 1 (by decide))).trans h.leftRows,
    (frame 2 (by decide) (by decide) (low 2 (by decide))).trans h.rightRows,
    (frame 3 (by decide) (by decide) (low 3 (by decide))).trans h.columns,?_,tbl,run.safe_end⟩
  intro j hj
  exact (frame (7+j) (by omega) (by omega) (by unfold tableBase; omega)).trans (h.entries j hj)

end Compression
end LinearProgramming
end Optimization
end OAI
