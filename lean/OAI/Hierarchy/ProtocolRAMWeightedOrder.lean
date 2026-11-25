import OAI.Hierarchy.TaggedShorterCommonScan
import OAI.Hierarchy.ProtocolRAMReportOrdinal

namespace OAI
/-! # Weighted stable order of a chronological word counter -/

noncomputable section
namespace Hierarchy.TaggedShorterReportedRank

open ProtocolRAMPortRanks ProtocolRAMReportedPorts TaggedShorterCommonScan
open scoped Classical BigOperators

theorem earlier_fin {n d : ℕ} (key : Fin n → Fin d) (width : Fin n → ℕ)
    (i : Fin n) (g : Fin d) :
    earlier key width i.val g=∑ j : Fin n, if j.val < i.val then
      (if key j=g then width j else 0) else 0 := by
  classical
  rw [←Finset.sum_filter]
  unfold earlier
  symm
  apply Finset.sum_bij (fun j _ => j.val)
  · intro j h
    exact Finset.mem_range.mpr (Finset.mem_filter.mp h).2
  · intro a _ b _ same
    exact Fin.ext same
  · intro j hj
    have before := Finset.mem_range.mp hj
    exact ⟨⟨j,before.trans i.isLt⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,before⟩,rfl⟩
  · intro j _
    simp [j.isLt]

/-- For any encoded group key and any stable permutation of the tape,
the native row counter is precisely the prefix on the typed group. -/
theorem earlier_prefix {n d : ℕ} (key : Fin n → Fin d) (g : Fin d)
    (P : Fin n → Prop) (groupKey : ∀ j, key j=g ↔ P j)
    (width rank : Fin n → ℕ) (sorted : Equiv.Perm (Fin n)) (i : {j // P j})
    (order : ∀ j, (sorted j).val < (sorted i.val).val ↔ rank j<rank i.val) :
    earlier (key ∘ sorted.symm) (width ∘ sorted.symm) (sorted i.val).val g =
      «prefix» (fun j : {j // P j} => width j.val) (fun j=>rank j.val) i := by
  classical
  rw [earlier_fin]
  let f (j : Fin n) := if rank j<rank i.val then width j else 0
  calc
    _ = ∑ j : Fin n, if P j then f j else 0 := by
      apply Fintype.sum_equiv sorted.symm
      intro j
      have ord := order (sorted.symm j)
      simp only [Equiv.apply_symm_apply] at ord
      simp only [Function.comp_apply,f,ord,groupKey]
      split_ifs <;> rfl
    _ = ∑ j ∈ Finset.univ.filter P, f j := (Finset.sum_filter P f).symm
    _ = _ := by
      rw [Finset.sum_subtype (p:=P) (Finset.univ.filter P) (fun _=>by simp) f]
      unfold «prefix»
      rw [Finset.sum_filter]

end Hierarchy.TaggedShorterReportedRank

end
end OAI
