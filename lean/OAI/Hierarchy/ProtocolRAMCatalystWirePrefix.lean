import OAI.Hierarchy.ProbeCatalystDatePrefix

namespace OAI
/-! # Per-owner reserve at an arbitrary prefix of the native debit rows -/
noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
variable {count payload : ℕ} (rowsAt : Event→ℕ) (owner : Event→ℕ→Fin count) (amount : Event→ℕ→ℕ)
def rankOwner (c : Mesh) (issued : Attempt→Entry count payload) (j : Fin (recordCount c issued)) : Fin count :=
  let z:=(rank c issued).symm j
  owner ((events c).get z.1) z.2.val

def ownerWithdrawal (event : Event) (target : Fin count) : ℕ :=
  match event with
  | .feed _ => 0
  | .attempt a =>
    ∑ i : Fin (rowsAt (.attempt a)), if owner (.attempt a) i.val=target then amount (.attempt a) i.val else 0

/-- Enumerating all originally issued row occurrences gives exactly the debit
at a single native date, including the repeated owners of distinct rows. -/
theorem ownerWithdrawal_eq (c : Mesh) (issued : Attempt→Entry count payload)
    (t : Fin (events c).length) (target : Fin count)
    (rows : (atTime c issued t).rows=rowsAt ((events c).get t))
    (posted : ∀i : Fin (atTime c issued t).rows,
      amount ((events c).get t) i.val=(atTime c issued t).bits i) :
    ownerWithdrawal rowsAt owner amount ((events c).get t) target =
      withdrawn c issued (rankOwner owner c issued) t target := by
  let event := (events c).get t
  have owner_read (i : Fin (atTime c issued t).rows) :
      rankOwner owner c issued (rank c issued ⟨t,i⟩) =
        owner ((events c).get t) i.val := by
    let selected : (Σ t,Fin (atTime c issued t).rows)→Fin count :=
      fun v=>owner ((events c).get v.1) v.2.val
    exact congrArg selected ((rank c issued).symm_apply_apply ⟨t,i⟩)
  cases here : event with
  | feed b =>
    have empty : (atTime c issued t).rows=0 := by
      change (eventEntry issued event).rows=0
      simp [here,eventEntry,noneEntry]
    have none : IsEmpty (Fin (atTime c issued t).rows) := ⟨fun i=>by have := i.isLt;omega⟩
    let := none
    change ownerWithdrawal rowsAt owner amount event target=_
    simp [here,ownerWithdrawal,withdrawn]
  | attempt a =>
    change ownerWithdrawal rowsAt owner amount event target=_
    have arity : (atTime c issued t).rows=rowsAt (.attempt a) := rows.trans (congrArg rowsAt here)
    rw [here,ownerWithdrawal,←(finCongr arity).sum_comp]
    unfold withdrawn
    apply Finset.sum_congr rfl
    intro i _
    rw [owner_read]
    change (if owner (.attempt a) i.val=target then
      amount (.attempt a) i.val else 0)=_
    have money := posted i
    change amount event i.val=_ at money
    change (if _ then _ else _)=(if owner event i.val=target then
      (atTime c issued t).bits i else 0)
    rw [here] at money ⊢
    rw [money]

theorem ownerWithdrawal_prefix (c : Mesh) (issued : Attempt→Entry count payload)
    (j : ℕ) (target : Fin count)
    (rows : ∀ t : Fin (events c).length,(atTime c issued t).rows=rowsAt ((events c).get t))
    (posted : ∀ (t : Fin (events c).length) (i : Fin (atTime c issued t).rows),
      amount ((events c).get t) i.val=(atTime c issued t).bits i) :
    (((events c).take j).map (fun ev=>ownerWithdrawal rowsAt owner amount ev target)).sum =
      usedBeforeDate c issued (rankOwner owner c issued) j target := by
  induction j with
  | zero => simp
  | succ j ih =>
    by_cases live : j < (events c).length
    · let t : Fin (events c).length := ⟨j,live⟩
      rw [show usedBeforeDate c issued (rankOwner owner c issued) (j+1) target =
        usedBeforeDate c issued (rankOwner owner c issued) j target+withdrawn c issued (rankOwner owner c issued) t target from
          usedBefore_succ c issued _ t target]
      simpa only [List.take_succ_eq_append_getElem live,List.map_append,List.map_cons,List.map_nil,
        List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,ih,List.get_eq_getElem,t]
        using congrArg (usedBeforeDate c issued (rankOwner owner c issued) j target+·)
          (ownerWithdrawal_eq rowsAt owner amount c issued t target (rows t) (posted t))
    · have pastEnd : (events c).length≤j:=Nat.le_of_not_gt live
      have right : usedBeforeDate c issued (rankOwner owner c issued) (j+1) target=
          usedBeforeDate c issued (rankOwner owner c issued) j target := by
        unfold usedBeforeDate
        exact Finset.sum_congr rfl fun t _=>by
          simp [t.isLt.trans_le pastEnd,t.isLt.trans_le (pastEnd.trans (Nat.le_succ j))]
      rw [List.take_of_length_le (pastEnd.trans (Nat.le_succ j)),right]
      simpa only [List.take_of_length_le pastEnd] using ih

/-- Flattening by the true native rank gives the exact aggregate stored by
the per-date reserve replay. The condition is on the original date of each
row, so a zero-arity feed contributes no records. -/
theorem usedBefore_rows (c : Mesh) (issued : Attempt→Entry count payload)
    (who : Fin (recordCount c issued)→Fin count) (j : ℕ) (target : Fin count) :
    usedBeforeDate c issued who j target = ∑ i : Fin (recordCount c issued),
      if ((rank c issued).symm i).1.val<j ∧ who i=target then debit c issued i else 0 := by
  let value (i : Fin (recordCount c issued)) :=
    if ((rank c issued).symm i).1.val<j ∧ who i=target then debit c issued i else 0
  change usedBeforeDate c issued who j target=∑ i,value i
  rw [←(rank c issued).sum_comp value,Fintype.sum_sigma]
  unfold usedBeforeDate
  apply Finset.sum_congr rfl
  intro t _
  by_cases prior : t.val<j
  · simp only [prior,ite_true,withdrawn,value,debit_at_rank,Equiv.symm_apply_apply,true_and]
  · simp only [prior,ite_false,value,debit_at_rank,Equiv.symm_apply_apply,false_and,Finset.sum_const_zero]

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
