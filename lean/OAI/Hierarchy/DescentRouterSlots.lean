import OAI.Hierarchy.DescentRouterBank

namespace OAI
/-! # Named actual terminals and local bundle words of a physical two-sided bank -/

namespace Hierarchy.DescentRouterSlots
open Computability.BorderVNP.Crossing DescentNamedContact DescentRouterBank
open scoped Classical BigOperators
noncomputable section
variable {I C R W : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W]
variable (D : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W) (wt : I→ℕ)
local notation "N" => network D contact input site owner wt
variable (s : Bool) (w : W)
abbrev InputId := {r : R // site s r=w}
abbrev LinkId := {c : C // owner s c=w}
abbrev Item := {i : I // owner s (contact i)=w}
def amount (i : Item contact owner s w) := wt i.val
def link (i : Item contact owner s w) : LinkId owner s w := ⟨contact i.val,i.property⟩
variable (align : ∀s i,site s (input s i)=owner s (contact i))
def root (i : Item contact owner s w) : InputId site s w := ⟨input s i.val,(align _ _).trans i.property⟩

def rootSlot (r : InputId site s w) : DescentNetworkSubstitution.Slot N (s,w) :=
  .inr (.inr ⟨(s,r.val),congrArg (Prod.mk s) r.property⟩)
def linkSlot : (s : Bool) → (w : W) → LinkId owner s w → DescentNetworkSubstitution.Slot N (s,w)
  | false,_,c => .inl ⟨c.val,congrArg (Prod.mk false) c.property⟩
  | true,_,c => .inr (.inl ⟨c.val,congrArg (Prod.mk true) c.property⟩)

def names : DescentNetworkSubstitution.Slot N (s,w) ≃ (InputId site s w ⊕ LinkId owner s w) where
  toFun
    | .inl e => .inr ⟨e.val,by
        have ha : false=s := congrArg Prod.fst e.property
        exact (congrArg (fun b => owner b e.val) ha.symm).trans (congrArg Prod.snd e.property)⟩
    | .inr (.inl e) => .inr ⟨e.val,by
        have ha : true=s := congrArg Prod.fst e.property
        exact (congrArg (fun b => owner b e.val) ha.symm).trans (congrArg Prod.snd e.property)⟩
    | .inr (.inr p) => .inl ⟨p.val.2,by
        have ha : p.val.1=s := congrArg Prod.fst p.property
        exact (congrArg (fun b => site b p.val.2) ha.symm).trans (congrArg Prod.snd p.property)⟩
  invFun := Sum.elim (rootSlot D contact input site owner wt s w) (linkSlot D contact input site owner wt s w)
  left_inv q := by
    rcases q with ⟨e,hit⟩|⟨e,hit⟩|⟨⟨t,r⟩,hit⟩
    · have h : false=s := congrArg Prod.fst hit
      subst s;rfl
    · have h : true=s := congrArg Prod.fst hit
      subst s;rfl
    · have h : t=s := congrArg Prod.fst hit
      subst s;rfl
  right_inv q := by rcases q with r|c <;> cases s <;> rfl

omit [Fintype R] in
@[simp] theorem names_root (r : InputId site s w) :
    names D contact input site owner wt s w (rootSlot D contact input site owner wt s w r)=.inl r := rfl
omit [Fintype R] in
@[simp] theorem names_link (c : LinkId owner s w) :
    names D contact input site owner wt s w (linkSlot D contact input site owner wt s w c)=.inr c := by cases s <;> rfl

def sourceWord (p : Ports (DescentNetworkSubstitution.slotWidth N (s,w))) (i : Item contact owner s w) :
    Fin (wt i.val)→Bool :=
  DescentContactTree.Physical.concat (fun t : Fibre (input s) (input s i.val)=>wt t.val)
    (p (rootSlot D contact input site owner wt s w (root contact input site owner s w align i))) ⟨i.val,rfl⟩

omit [Fintype R] in
theorem linkWidth (c : LinkId owner s w) : DescentNetworkSubstitution.slotWidth N (s,w)
    (linkSlot D contact input site owner wt s w c)=width contact wt c.val := by cases s <;> rfl

def targetWord (p : Ports (DescentNetworkSubstitution.slotWidth N (s,w))) (i : Item contact owner s w) :
    Fin (wt i.val)→Bool :=
  DescentContactTree.Physical.concat (fun t : Fibre contact (contact i.val)=>wt t.val)
    (fun j=>p (linkSlot D contact input site owner wt s w (link contact owner s w i))
      (Fin.cast (linkWidth D contact input site owner wt s w _).symm j)) ⟨i.val,rfl⟩

omit [Fintype R] in
theorem source_feed (x : Bool→DescentContactTree.Physical.Row wt) (z : DescentContactTree.Physical.Row wt)
    (i : Item contact owner s w) :
    sourceWord D contact input site owner wt s w align (feed D contact input site owner wt x z s w) i=x s i.val := by
  change (labels (input s) wt) ((labels (input s) wt).symm (x s)) i.val = x s i.val
  exact congrFun ((labels (input s) wt).apply_symm_apply (x s)) i.val

omit [Fintype R] in
theorem target_feed (x : Bool→DescentContactTree.Physical.Row wt) (z : DescentContactTree.Physical.Row wt)
    (i : Item contact owner s w) :
    targetWord D contact input site owner wt s w (feed D contact input site owner wt x z s w) i=z i.val := by
  cases s <;> change (labels contact wt) ((labels contact wt).symm z) i.val = z i.val
  all_goals exact congrFun ((labels contact wt).apply_symm_apply z) i.val

omit [Fintype R] in
theorem word_agreement (x : Bool→DescentContactTree.Physical.Row wt) (z : DescentContactTree.Physical.Row wt) :
    (sourceWord D contact input site owner wt s w align (feed D contact input site owner wt x z s w)=
      targetWord D contact input site owner wt s w (feed D contact input site owner wt x z s w)) ↔
      ∀i,owner s (contact i)=w → x s i=z i := by
  constructor
  · intro all i atw
    simpa only [source_feed,target_feed] using congrFun all ⟨i,atw⟩
  · intro all
    funext i
    rw [source_feed,target_feed,all i.val i.property]

end
end Hierarchy.DescentRouterSlots

end OAI
