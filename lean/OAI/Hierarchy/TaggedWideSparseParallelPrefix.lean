import OAI.Hierarchy.ProtocolRAMWeightedOrder

namespace OAI
/-! # Relative weighted offsets in two lists of live parallel records -/

namespace Hierarchy.TaggedShorterReportedRank
open scoped Classical BigOperators

/-- Relative order is required only for positive-width rows with the same key. -/
theorem sparse_parallel_prefix {n m d : ℕ}
    (src : Fin n→Fin d) (dst : Fin m→Fin d) (amt : Fin n→ℕ) (mass : Fin m→ℕ)
    (row : Fin n↪Fin m) (counts : ∀i,mass (row i)=amt i)
    (absent : ∀i,i∉Set.range row→mass i=0)
    (matchKey : ∀i,0<amt i→dst (row i)=src i)
    (prior : ∀i j,0<amt i→0<amt j→src i=src j→(i<j ↔ row i<row j))
    (i:Fin n) (live : 0<amt i) :
    TaggedShorterCommonScan.earlier src amt i.val (src i)=
      TaggedShorterCommonScan.earlier dst mass (row i).val (dst (row i)) := by
  rw [earlier_fin,earlier_fin]
  apply Fintype.sum_of_injective row row.injective
  · intro x hx
    simp [absent x hx]
  · intro j
    by_cases positive : 0<amt j
    · rw [matchKey i live,matchKey j positive,counts]
      by_cases same : src j=src i
      · have ord : (j.val < i.val) ↔ ((row j).val < (row i).val) := prior j i positive live same
        simp [same,ord]
      · simp [same]
    · simp [counts,Nat.eq_zero_of_not_pos positive]

end Hierarchy.TaggedShorterReportedRank

end OAI
