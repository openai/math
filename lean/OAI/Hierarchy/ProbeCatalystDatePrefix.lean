import OAI.Hierarchy.ProbeCatalystDateTotal

namespace OAI
/-! # The reserve used before and after one originally dated native withdrawal -/
noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical
variable {count payload : ℕ} (c : Mesh) (issued : Attempt→Entry count payload)

def withdrawn (site : Fin (recordCount c issued)→Fin count) (t : Fin (events c).length)
    (key : Fin count) :=
  ∑i : Fin (atTime c issued t).rows,if site (rank c issued ⟨t,i⟩)=key then (atTime c issued t).bits i else 0

def usedBeforeDate (site : Fin (recordCount c issued)→Fin count) (date : ℕ) (key : Fin count) :=
  ∑t : Fin (events c).length,if t.val<date then withdrawn c issued site t key else 0

@[simp] theorem usedBefore_zero (site : Fin (recordCount c issued)→Fin count) (key : Fin count) :
    usedBeforeDate c issued site 0 key=0 := by simp [usedBeforeDate]

theorem usedBefore_succ (site : Fin (recordCount c issued)→Fin count) (t : Fin (events c).length) (key : Fin count) :
    usedBeforeDate c issued site (t.val+1) key=usedBeforeDate c issued site t.val key+withdrawn c issued site t key := by
  let weight := fun j : Fin (events c).length=>withdrawn c issued site j key
  have row (j : Fin (events c).length) :
      (if j.val<t.val+1 then weight j else 0)=
        (if j.val<t.val then weight j else 0)+(if j=t then weight j else 0) := by
    by_cases eq : j=t
    · subst j;simp
    · have diff : j.val≠t.val := fun eqv=>eq (Fin.ext eqv)
      by_cases prior : j.val<t.val
      · simp [prior,eq,Nat.lt_succ_of_lt prior]
      · simp [prior,eq,show ¬j.val<t.val+1 by omega]
  change (∑ j,if j.val<t.val+1 then weight j else 0)=
    (∑ j,if j.val<t.val then weight j else 0)+weight t
  calc
    _ = ∑ j,((if j.val<t.val then weight j else 0)+(if j=t then weight j else 0)) :=
      Finset.sum_congr rfl (fun j _=>row j)
    _ = _ := by rw [Finset.sum_add_distrib];simp

/-- At a dependent-pair rank, the stored weight is the original cell's weight. -/
theorem debit_at_rank (t : Fin (events c).length) (i : Fin (atTime c issued t).rows) :
    debit c issued (rank c issued ⟨t,i⟩)=(atTime c issued t).bits i := by
  let value := fun x : (Σ t,Fin (atTime c issued t).rows)=>(atTime c issued x.1).bits x.2
  exact congrArg value ((rank c issued).symm_apply_apply ⟨t,i⟩)

theorem usedBefore_last (site : Fin (recordCount c issued)→Fin count) (key : Fin count) :
    usedBeforeDate c issued site (events c).length key=∑j,if site j=key then debit c issued j else 0 := by
  rw [←(rank c issued).sum_comp (fun j=>if site j=key then debit c issued j else 0),Fintype.sum_sigma]
  simp only [usedBeforeDate,Fin.is_lt,ite_true,withdrawn,debit_at_rank]

theorem usedBefore_le (site : Fin (recordCount c issued)→Fin count) (key : Fin count) (date : ℕ) {reserve : ℕ}
    (funded : (∑j,if site j=key then debit c issued j else 0)≤reserve) :
    usedBeforeDate c issued site date key≤reserve := by
  rw [←usedBefore_last c issued site key] at funded
  apply le_trans _ funded
  apply Finset.sum_le_sum
  intro t _
  by_cases small : t.val<date <;> simp [small,t.isLt]

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
