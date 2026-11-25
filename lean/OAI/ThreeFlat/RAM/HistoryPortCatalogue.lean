import OAI.ThreeFlat.RAM.HistoryPartyCatalogueData
import OAI.ThreeFlat.RAM.HistoryPartyImage

namespace OAI
/-! # Immutable bounded port tables for the selected grid tile -/

namespace ThreeFlat.RAM.HistoryPortCatalogue

open Computability.VPVNP.BurstRAM
open scoped BigOperators Classical
noncomputable section
variable {n e D E : ℕ}

theorem demand_row (G : Page n e) (max : n≤D) (u : Fin n) :
    G.at D E (demandBase+2*u.val)=G.demand u ∧ G.at D E (demandBase+2*u.val+1)=G.baseWidth u := by
  have h := u.isLt
  have second : (3+u.val*2-2)/2 = u.val := by omega
  simp (disch := omega) [Page.at,demandBase,supplyBase,second,Nat.mul_comm 2 u.val,
    show 3+u.val*2<3+2*D by omega,show 3+u.val*2+1<3+2*D by omega,u.isLt]; split_ifs <;> omega

theorem supply_row (G : Page n e) (max : e≤E) (u : Fin e) :
    G.at D E (supplyBase D+u.val)=G.supply u := by
  have h := u.isLt
  simp (disch := omega) [Page.at,headerBase,supplyBase,u.isLt,
    show 3+2*D+u.val<3+2*D+E by omega]; split_ifs <;> omega

theorem digits_row (G : Page n e) (u : Fin n) (b : Fin (G.baseWidth u)) :
    let q := (finSigmaFinEquiv ⟨u,b⟩).val
    G.at D E (headerBase D E+2*q)=u.val ∧ G.at D E (headerBase D E+2*q+1)=b.val := by
  let q : Fin G.digits := finSigmaFinEquiv ⟨u,b⟩
  have h := q.isLt
  have inv : G.decode q=⟨u,b⟩ := finSigmaFinEquiv.symm_apply_apply _
  change G.at D E (headerBase D E+2*q.val)=_ ∧ G.at D E (headerBase D E+2*q.val+1)=_
  have read (lane : Fin 2) :
      G.at D E (headerBase D E+(2*q.val+lane.val)) =
        if lane.val=0 then (G.decode q).1.val else (G.decode q).2.val := by
    let addr := headerBase D E+(2*q.val+lane.val)
    have baseRoom : 3 ≤ headerBase D E := by dsimp [headerBase,supplyBase]; omega
    have rowsRoom : supplyBase D ≤ headerBase D E := Nat.le_add_right _ _
    have afterHeader : headerBase D E ≤ addr := Nat.le_add_right _ _
    have offset : addr-headerBase D E=2*q.val+lane.val := Nat.add_sub_cancel_left _ _
    have lo := lane.isLt
    have index : (2*q.val+lane.val)/2 = q.val := by omega
    have column : (2*q.val+lane.val)%2 = lane.val := by omega
    change G.at D E addr = _
    simp only [Page.at,ite_eq_right (by omega : addr≠0),ite_eq_right (by omega : addr≠1),
      ite_eq_right (by omega : addr≠2),ite_eq_right (by omega : ¬ addr < supplyBase D),
      ite_eq_right (by omega : ¬ addr < headerBase D E),offset,index,column,dite_eq_left h]
    split
    · rfl
    · apply congrArg (fun i : Fin G.digits => (G.decode i).2.val)
      exact Fin.ext (by change (addr-headerBase D E)/2 = q.val; rw [offset,index])
  constructor
  · simpa only [Fin.val_zero,Nat.add_zero,ite_true,inv] using read 0
  · refine Eq.trans ?_ (congrArg (fun x : (Σ v, Fin (G.baseWidth v)) => x.2.val) inv)
    simpa only [Fin.val_one,Nat.add_assoc,one_ne_zero,ite_false] using read 1

end


end ThreeFlat.RAM.HistoryPortCatalogue

end OAI
