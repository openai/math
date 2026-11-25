import OAI.Hierarchy.DescentMixedRouter

namespace OAI
/-! # First segments at merged hubs, including contacts of directory depth zero -/

namespace Hierarchy.DescentTetherPorts
open Computability.BorderVNP.Crossing DescentRouterSlots DescentRotor DescentMixedRouter DescentContactTree
open scoped Classical BigOperators
noncomputable section
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable {n h C₀ bits D : ℕ} (G : NonlinearExpanders.Graph n h) (hw : 0<bits)
variable (u : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i))
local notation "wt" => fun _ : I=>u
local notation "B" => DescentRouterBank.network D contact input site owner wt
local notation "Ch" => Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align
local notation "Device" => device G hw u contact input site owner align (D:=D)
variable {s : Bool} {w : W}

/-- Root predicate on the actual physical vertices of a selected device. -/
def isRoot : (c : Ch s w) → (Device c).Site → Prop
  | .exceptional _,v => v.1.val=0
  | .good ..,_ => False

/-- When the only potential contact is already the root, its direct cable is
the first real segment. No private tree wire is present in that case. -/
def direct : Ch s w → Prop
  | .exceptional t => t.book.height=0
  | .good .. => False

def hasTree : Ch s w → Prop
  | .exceptional _ => True
  | .good .. => False

def mass (s : Bool) (w : W) := ∑_i : Item contact owner s w,u

omit [Fintype R] in
theorem direct_root (c : Ch s w) (edge : LinkId owner s w) :
    isRoot G hw u contact input site owner align c
      ((Device c).attach (linkSlot D contact input site owner wt s w edge)) ↔
      direct G hw u contact input site owner align c := by
  cases c with
  | good first last pay circuit => rfl
  | exceptional _ =>
    simp [isRoot,direct,device,DescentFixedExceptionalRouter.device,DescentExceptionalRouter.position,
      DescentFixedNamedContact.network,DescentFixedNamedContact.place,DescentLocalAdapters.graph,
      Physical.graph,DescentFixedNamedContact.paddedTree]

private theorem branch_sum {J : Type} [Fintype J] (dest : J→ℕ→Bool) (wgt : J→ℕ) (k : ℕ) :
    (∑e : Physical.Edge k,if e.1.val=0 then Physical.nodeWidth dest wgt (e.1.val+1) e.2 else 0) =
    if k=0 then 0 else ∑i,wgt i := by
  cases k with
  | zero => simp [Physical.Edge]
  | succ k =>
    rw [Fintype.sum_sigma]
    rw [Fin.sum_univ_succ]
    simp [Physical.nodeWidth]
    exact level_width wgt 1 dest

omit [Fintype R] in
theorem private_first (c : Ch s w) :
    (∑ e : (Device c).Edge,if isRoot G hw u contact input site owner align c ((Device c).src e) ∨
      isRoot G hw u contact input site owner align c ((Device c).dst e) then (Device c).width e else 0)=
      if hasTree G hw u contact input site owner align c ∧ ¬direct G hw u contact input site owner align c
      then mass u contact owner s w else 0 := by
  cases c with
  | good first last pay circuit => simp [isRoot,direct,hasTree]
  | exceptional root =>
    let k := root.book.height
    let dest := DescentFixedNamedContact.code root.book.codes (link contact owner s w)
    let weight := amount contact owner wt s w
    let c : Ch s w := .exceptional root
    calc
      _ = ∑ e : Physical.Edge k, if e.1.val=0 then Physical.nodeWidth dest weight (e.1.val+1) e.2 else 0 := by
        apply Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
        intro e _
        by_cases first : e.1.val=0
        · have hit : isRoot G hw u contact input site owner align c ((Device c).src e) := first
          exact (ite_eq_left (Or.inl hit)).trans (ite_eq_left first).symm
        · have away : ¬(isRoot G hw u contact input site owner align c ((Device c).src e) ∨
              isRoot G hw u contact input site owner align c ((Device c).dst e)) := by
            rintro (source | target)
            · exact first source
            · exact Nat.succ_ne_zero e.1.val target
          exact (ite_eq_right away).trans (ite_eq_right first).symm
      _ = if k=0 then 0 else ∑i,weight i := branch_sum dest weight k
      _ = _ := by
        by_cases empty : k=0
        · exact (ite_eq_left empty).trans (ite_eq_right (fun endpoints => endpoints.2 empty)).symm
        · exact (ite_eq_right empty).trans (ite_eq_left ⟨True.intro,empty⟩).symm

theorem owner_mass (keep : W→Prop) (s : Bool) :
    (∑c,if keep (owner s c) then DescentNamedContact.width contact wt c else 0)=
      ∑w,if keep w then mass u contact owner s w else 0 := by
  let f (i : I) := if keep (owner s (contact i)) then u else 0
  have lhs : (∑c,if keep (owner s c) then DescentNamedContact.width contact wt c else 0)=∑i,f i := by
    rw [←(Equiv.sigmaFiberEquiv contact).sum_comp f,Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro c _
    change (if keep (owner s c) then ∑ _i : DescentNamedContact.Fibre contact c, u else 0) =
      ∑ i : DescentNamedContact.Fibre contact c, f i.val
    calc
      _ = ∑ _i : DescentNamedContact.Fibre contact c, (if keep (owner s c) then u else 0) := by
        by_cases yes : keep (owner s c) <;> simp [yes]
      _ = _ := Finset.sum_congr rfl (fun i _ => by simp only [f, i.property])
  rw [lhs,←(Equiv.sigmaFiberEquiv (fun i=>owner s (contact i))).sum_comp f,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro w _
  change (∑ i : Item contact owner s w, f i.val) = if keep w then mass u contact owner s w else 0
  calc
    _ = ∑ _i : Item contact owner s w, (if keep w then u else 0) :=
      Finset.sum_congr rfl (fun i _ => by simp only [f, i.property])
    _ = _ := by by_cases yes : keep w <;> simp [yes, mass]

end
end Hierarchy.DescentTetherPorts

end OAI
