import OAI.Hierarchy.DescentTreePrefixIntervals
import OAI.Hierarchy.DescentFixedExceptionalRouter

namespace OAI
/-! # The real fallback tree's parent cable is an interval of arrived original grain addresses -/

namespace Hierarchy.DescentPrivateTreeWidths
open DescentTreePrefixIntervals DescentContactTree Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section

variable {I C : Type} [Fintype I] [Fintype C] {h H : ℕ}

def leaf (book : C↪Node h) (contact : I→C) (ceiling : ℕ) (i : I) :=
  start ceiling (book (contact i))

omit [Fintype C] in
theorem physical_width (book : C↪Node h) (contact : I→C) (wt : I→ℕ) (D : ℕ)
    (room : h≤H) (e : Physical.Edge h) :
    (DescentFixedNamedContact.network book contact wt D).width e =
      ∑i,if start H e.2 ≤ leaf book contact H i ∧ leaf book contact H i < stop H e.2 then wt i else 0 := by
  let name:=DescentFixedNamedContact.code book contact
  have fine : e.1.val+1≤h :=e.1.isLt
  have same (i : I) : prefixAt name (e.1.val+1) i=cut fine (book (contact i)) := by
    funext j
    simp [name,prefixAt,DescentFixedNamedContact.code,cut,j.isLt.trans_le fine]
    apply congrArg (book (contact i))
    exact Fin.ext rfl
  change (∑i : Cell name (e.1.val+1) e.2,wt i.val)=_
  rw [←Finset.sum_subtype (Finset.univ.filter (fun i=>prefixAt name (e.1.val+1) i=e.2))
      (by simp) wt,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  have agrees : prefixAt name (e.1.val+1) i=e.2 ↔
      start H e.2≤leaf book contact H i ∧ leaf book contact H i<stop H e.2 := by
    rw [same i]
    exact (member fine room (book (contact i)) e.2).symm
  by_cases hit : prefixAt name (e.1.val+1) i=e.2
  · simp only [ite_eq_left hit,ite_eq_left (agrees.mp hit)]
  · simp only [ite_eq_right hit,ite_eq_right (fun h => hit (agrees.mpr h))]

variable {R W : Type} [Fintype R] [Fintype W]
open DescentRouterSlots

omit [Fintype R] in
/-- Both orientations use the actual source-side ownership test and that side's actual contact book. -/
theorem device_width (D : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W)
    (owner : Bool→C→W) (wt : I→ℕ) (side : Bool) (root : W)
    (book : LinkId owner side root ↪ Node h) (wide : h≤H) (e : Physical.Edge h) :
    (DescentFixedExceptionalRouter.device D contact input site owner wt side root book).width e =
      ∑i : Item contact owner side root,
        if start H e.2≤leaf book (link contact owner side root) H i ∧
           leaf book (link contact owner side root) H i<stop H e.2 then wt i.val else 0 :=
  physical_width book (link contact owner side root) (amount contact owner wt side root) D wide e

omit [Fintype R] in
theorem endpoints (D : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W)
    (owner : Bool→C→W) (wt : I→ℕ) (side : Bool) (root : W)
    (book : LinkId owner side root ↪ Node h) (e : Physical.Edge h) :
    let N:=DescentFixedExceptionalRouter.device D contact input site owner wt side root book
    N.src e=⟨e.1.castSucc,fun i=>e.2 i.castSucc⟩ ∧ N.dst e=⟨e.1.succ,e.2⟩ := ⟨rfl,rfl⟩

end
end Hierarchy.DescentPrivateTreeWidths

end OAI
