import OAI.Hierarchy.DescentPhysicalResetDateTariff
import OAI.Hierarchy.DescentResetMixedInputWork

namespace OAI
/-! # Instruction counts of the five rank fields and nine candidate-mask fields -/
namespace Hierarchy.DescentDatedAddressBook
open DescentPackedZip DescentPacking.PackedMatch.Local ProtocolRAM
noncomputable section

def compiledSourceWork (D : ℕ) := 200*(mixedSourceWork D+1)

private theorem assembled_work {n : ℕ} (table : Fin n→Tables) (field : Fin n→Expr) (T : ℕ)
    (small : ∀i,(field i).work≤T) :
    (Gather.assembly table field).work ≤ 1+n*(T+11) := by
  have bound (xs : List (Fin n)) : (Gather.collect table field xs).work≤1+xs.length*(T+11) := by
    induction xs with
    | nil => simp [Gather.collect,Expr.work]
    | cons i is ih =>
      have next := small i
      simp only [Gather.collect,DescentPackedZip.work,List.length_cons,Nat.succ_mul]
      omega
  simpa only [Gather.assembly,List.length_finRange] using bound (List.finRange n)

namespace PhysicalReset
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)

theorem DateInputs.masked_work :
    rankWork u ≤ compiledSourceWork a.successor.front.peer.oldDegree ∧
      maskWork u ≤ compiledSourceWork a.successor.front.peer.oldDegree := by
  let T := mixedSourceWork a.successor.front.peer.oldDegree
  let m := u.masked.mixed
  obtain ⟨r,s⟩ := u.masked_input_work
  change (∀j i,(m.rankReads j i).work≤T) at r
  change (∀j i,(m.rawReads j i).work≤T) at s
  have field (j : ℕ) (i : Fin 9) : (m.fields j i).work ≤ T+7 := by
    unfold DescentResetCandidateDate.Mixed.fields
    split
    · change 7≤T+7
      omega
    · exact (s j i).trans (Nat.le_add_right ..)
  constructor
  · unfold rankWork peak
    apply Finset.sup_le
    intro i _
    apply (assembled_work _ (m.rankReads i.val) T (r i.val)).trans
    change 1+5*(T+11) ≤ 200*(T+1)
    omega
  · unfold maskWork peak
    apply Finset.sup_le
    intro i _
    apply (assembled_work _ (m.fields i.val) (T+7) (field i.val)).trans
    change 1+9*((T+7)+11) ≤ 200*(T+1)
    omega

end PhysicalReset
end
end Hierarchy.DescentDatedAddressBook

end OAI
