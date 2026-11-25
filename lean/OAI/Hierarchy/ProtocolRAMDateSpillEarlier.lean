import OAI.Hierarchy.TaggedShorterCommonScan

namespace OAI
/-! # Removing the zero-weight permanent edge prefix from the dated spill ranks -/

namespace Hierarchy.ProtocolRAMDateSpillRank
open scoped BigOperators

theorem earlier_tail {edges r d : ℕ} (key : Fin (edges+r)→Fin d) (width : Fin (edges+r)→ℕ)
    (tailKey : Fin r→Fin d) (tailWidth : Fin r→ℕ)
    (zeroHead : ∀i : Fin edges,width (i.castAdd r)=0)
    (keys : ∀i : Fin r,key (i.natAdd edges)=tailKey i)
    (widths : ∀i : Fin r,width (i.natAdd edges)=tailWidth i)
    (t : Fin r) (e : Fin d) :
    TaggedShorterCommonScan.earlier key width (edges+t.val) e=
      TaggedShorterCommonScan.earlier tailKey tailWidth t.val e := by
  unfold TaggedShorterCommonScan.earlier
  rw [Finset.sum_range_add]
  have zero : (∑ j ∈ Finset.range edges, if h : j<edges+r then
      (if key ⟨j,h⟩=e then width ⟨j,h⟩ else 0) else 0)=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have small:=Finset.mem_range.mp hj
    have fit : j<edges+r := by omega
    rw [dite_eq_left fit]
    have value : width ⟨j,fit⟩=0 := zeroHead ⟨j,small⟩
    simp [value]
  rw [zero,Nat.zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  have small : j<r := (Finset.mem_range.mp hj).trans t.isLt
  rw [dite_eq_left small,dite_eq_left (Nat.add_lt_add_left small edges)]
  change (if key ((⟨j,small⟩ : Fin r).natAdd edges)=e then
    width ((⟨j,small⟩ : Fin r).natAdd edges) else 0)=_
  rw [keys,widths]

end Hierarchy.ProtocolRAMDateSpillRank

end OAI
