import OAI.Hierarchy.TraceReceiverRunCost
import OAI.Hierarchy.TraceReceiverVisitTariff
import OAI.Hierarchy.TraceResourceComposite

namespace OAI
/-! # Charging the native selected loop to the exact scheduler fiber -/

namespace Hierarchy.TraceReceiverRunCost
open ThreeFlat Diagonal PhysicalStage NavigationPass
open HistoryContraction RAM RAM.NavigationNodeRows RAM.HistoryNodeDirectory RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM PrivateRAM FactorAllocation
open scoped Classical BigOperators Fin.CommRing
noncomputable section

/-- Physical final ordinals agree with the canonical ordering used to index
the S43 resource publisher, at this same selector and history. -/
theorem registered_work {F : Type} [Field F] {d l : ℕ} {A : State d l}
    (r : Run F A) (h : r.plan.History) (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O)
    (num : r.FinalNumbered h C O p) (start : A.Site→ℕ)
    (count : Fintype.card (r.plan.finish h).Site=(r.finalArchive h C O p).1.count)
    (v : Fin (r.finalArchive h C O p).1.count) :
    r.rootArray h C start ((r.finalArchive h C O p).2.symm v)=
      r.chargeAt h C start ((TraceAdmission.Resources.indexEquiv r h count).symm v) := by
  let x:=(r.finalSite h) ((r.finalArchive h C O p).2.symm v)
  have key : TraceAdmission.Resources.indexEquiv r h count x=v := by
    apply Fin.ext
    change (r.terminalOrderEquiv h x).val=v.val
    calc
      _ = ((r.finalArchive h C O p).2 ((r.finalSite h).symm x)).val := by
        rw [r.terminalOrderEquiv_val]
        exact (num _).symm
      _ = _ := by simp only [x,Equiv.symm_apply_apply,Equiv.apply_symm_apply]
  have back : (TraceAdmission.Resources.indexEquiv r h count).symm v=x :=
    by rw [←key,Equiv.symm_apply_apply]
  rw [back]
  simp [Run.chargeAt,x]

private theorem fiber_indicator {ι : Type} [Fintype ι] {p : ι→Prop} [DecidablePred p] (cost : ι→ℕ) :
    (∑i : {i // p i},cost i.val)=∑i,if p i then cost i else 0 := by
  let cash (i : ι) := if p i then cost i else 0
  have yes (i : {i // p i}) : cash i.val = cost i.val := ite_eq_left i.property
  have no (i : {i // ¬p i}) : cash i.val = 0 := ite_eq_right i.property
  change _ = ∑ i, cash i
  rw [←Fintype.sum_subtype_add_sum_subtype p cash]
  simp only [yes, no, Finset.sum_const_zero, add_zero]

/-- The hardware ABI permits all machine words as root labels. Only labels
corresponding to genuine final factors can contribute to the clock, even
when tick zero is being run. -/
theorem selected_sum {W f n T dim : ℕ} (ht : 0<T) (w : ℕ) (cost : Fin n→Fin dim→ℕ)
    (tick : Fin T) (chron : Chronology (f+n)) (first : chron.firstFinal=f)
    (rootFit : n≤2^W) (tickFit : T≤2^W) (expense : Fin (f+n)→ℕ) (work : Fin n→ℕ)
    (subtree : ∀r:Fin n,(∑i:{i:Fin (f+n) // chron.root i=r.val},expense i.val)≤work r) :
    let D:=TraceReceiverOwnerMount.directory chron
      (fun r=>((FactorAllocation.owner ht w cost r).val:Word W)) (tick.val:Word W)
    (∑ k : Word W, if D.owner k=(D.group,D.slot) then
      ∑i : {i : Fin (f+n) // D.root i=k},expense i.val else 0) ≤
      ((FactorAllocation.factors w cost (List.finRange n) tick).map work).sum := by
  classical
  let D:=TraceReceiverOwnerMount.directory chron (fun r=>((FactorAllocation.owner ht w cost r).val:Word W))
    (tick.val:Word W)
  let fee (k : Word W):=if D.owner k=(D.group,D.slot) then
    ∑i : {i : Fin (f+n) // D.root i=k},expense i.val else 0
  let L:=FactorAllocation.factors w cost (List.finRange n) tick
  change (∑k,fee k)≤(L.map work).sum
  have valid (i : Fin (f+n)) : chron.root i<n := by
    have hi:=chron.root_lt i
    rw [first] at hi
    omega
  have word (i : Fin (f+n)) : (D.root i).val=chron.root i :=
    Fin.val_cast_of_lt ((valid i).trans_le rootFit)
  have null (k : Word W) (outside : ¬k.val<n) : fee k=0 := by
    have no (i : Fin (f+n)) : D.root i≠k:=by
      intro eqn
      have val := congrArg Fin.val eqn
      rw [word] at val
      exact outside (val ▸ valid i)
    simp [fee,fiber_indicator,no]
  let E : {k:Word W // k.val<n} ≃ Fin n :=
    { toFun:=fun k=>⟨k.val.val,k.property⟩
      invFun:=fun i=>⟨⟨i.val,i.isLt.trans_le rootFit⟩,i.isLt⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
  have split:=Fintype.sum_subtype_add_sum_subtype (fun k:Word W=>k.val<n) fee
  have void : (∑k : {k:Word W // ¬k.val<n},fee k.val)=0 := Finset.sum_eq_zero fun k _=>null k.val k.property
  rw [void,add_zero] at split
  rw [←split,←E.symm.sum_comp (fun k=>fee k.val)]
  have costSmall (i : Fin n) : fee (E.symm i).val≤ if i∈L then work i else 0 := by
    let row:Word W:=⟨i.val,i.isLt.trans_le rootFit⟩
    have words (j : Fin (f+n)) : D.root j=row ↔ chron.root j=i.val := by
      rw [Fin.ext_iff,word]
    let desc:=FactorAllocation.owner ht w cost i
    have elected : D.owner row=(D.group,D.slot) ↔ desc=tick := by
      change (0,(if h:row.val<n then ((FactorAllocation.owner ht w cost ⟨row.val,h⟩).val:Word W) else 0))=(0,(tick.val:Word W)) ↔ _
      rw [dite_eq_left i.isLt, Prod.mk.injEq]
      change (_ ∧ (desc.val : Word W) = (tick.val : Word W)) ↔ desc = tick
      constructor
      · intro h
        apply Fin.ext
        exact (Fin.val_cast_of_lt (desc.isLt.trans_le tickFit)).symm.trans
          ((congrArg Fin.val h.2).trans (Fin.val_cast_of_lt (tick.isLt.trans_le tickFit)))
      · intro h
        exact ⟨rfl, congrArg (fun x : Fin T => (x.val : Word W)) h⟩
    have member : i∈L ↔ desc=tick:=(FactorAllocation.mem_factors_iff_owner ht w cost i tick).trans eq_comm
    change (if D.owner row=(D.group,D.slot) then _ else _)≤_
    by_cases yes : i∈L
    · rw [ite_eq_left yes,ite_eq_left (elected.mpr (member.mp yes)),fiber_indicator]
      change (∑ j : Fin (f+n), if D.root j=row then expense j else 0) ≤ work i
      simp_rw [words]
      rw [←fiber_indicator]
      exact subtree i
    · rw [ite_eq_right yes,ite_eq_right (fun e=>yes (member.mpr (elected.mp e)))]
  have total:=Finset.sum_le_sum (s:=Finset.univ) fun i _=>costSmall i
  refine total.trans_eq ?_
  rw [← List.sum_toFinset _ (FactorAllocation.factors_nodup ht w cost tick)]
  rw [←Finset.sum_filter]
  exact Finset.sum_congr (by ext;simp [L]) (fun _ _=>rfl)

end
end Hierarchy.TraceReceiverRunCost

end OAI
