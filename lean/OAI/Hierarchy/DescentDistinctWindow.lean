import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Order.Nat
import Mathlib.Tactic

namespace OAI
/-! # The number of active private word addresses in bounded consecutive site rows -/

namespace Hierarchy.DescentDistinctWindow
open scoped BigOperators Classical
noncomputable section
variable {n : ℕ} {A : Type} [DecidableEq A] (tags : Fin n→Option A)

def AtGap (i : Fin n) (d : ℕ) : Prop := ∃ j : Fin n,j.val+d=i.val ∧ tags j=tags i
def Fresh (K : ℕ) (i : Fin n) : Prop :=
  (tags i).isSome=true ∧ ∀d,0<d→d≤K→¬AtGap tags i d
def Occupied (a : A) : Prop := ∃i,tags i=some a

/-- Each site's operand slots occupy an interval of length at most K+1. -/
def Local (K : ℕ) : Prop := ∀i j : Fin n,j.val < i.val→tags i=tags j→(tags i).isSome=true→i.val-j.val≤K

variable {K : ℕ}

omit [DecidableEq A] in
private theorem no_prior (h : Local tags K) (i : Fin n) :
    Fresh tags K i ↔ (tags i).isSome=true ∧ ∀j : Fin n,j.val < i.val→tags j≠tags i := by
  constructor
  · intro fr
    refine ⟨fr.1,?_⟩
    intro j lt eqn
    exact fr.2 (i.val-j.val) (by omega) (h i j lt eqn.symm fr.1) ⟨j,by omega,eqn⟩
  · intro fr
    refine ⟨fr.1,?_⟩
    rintro d pos _ ⟨j,gap,eqn⟩
    exact fr.2 j (by omega) eqn

private def first (a : A) (ok : Occupied tags a) : Fin n :=
  ⟨Nat.find (show ∃k : ℕ,∃i : Fin n,i.val=k ∧ tags i=some a from
      ⟨ok.choose.val,ok.choose,rfl,ok.choose_spec⟩),
    by
      obtain ⟨i,h,_⟩:=Nat.find_spec (show ∃k : ℕ,∃i : Fin n,i.val=k ∧ tags i=some a from
        ⟨ok.choose.val,ok.choose,rfl,ok.choose_spec⟩)
      exact h ▸ i.isLt⟩

private theorem first_read (a : A) (ok : Occupied tags a) : tags (first tags a ok)=some a := by
  obtain ⟨i,h,yes⟩:=Nat.find_spec (show ∃k : ℕ,∃i : Fin n,i.val=k ∧ tags i=some a from
    ⟨ok.choose.val,ok.choose,rfl,ok.choose_spec⟩)
  have same : first tags a ok=i := Fin.ext h.symm
  exact (congrArg tags same).trans yes

private theorem first_le (a : A) (ok : Occupied tags a) (i : Fin n) (read : tags i=some a) :
    (first tags a ok).val≤ i.val := Nat.find_min' _ ⟨i,rfl,read⟩

/-- Finite occupied addresses and successful native first-write tests name the same set. -/
def representatives (h : Local tags K) : {i // Fresh tags K i} ≃ {a //Occupied tags a} where
  toFun i:=⟨(tags i.val).get i.property.1, i.val,(Option.some_get i.property.1).symm⟩
  invFun a:=⟨first tags a.val a.property,(no_prior tags h _).2 ⟨by
    simp only [first_read tags a.val a.property,Option.isSome_some],by
    intro j lt eqn
    exact (Nat.not_lt_of_ge (first_le tags a.val a.property j
      (eqn.trans (first_read tags a.val a.property)))) lt⟩⟩
  left_inv i:=by
    apply Subtype.ext
    let a:=(tags i.val).get i.property.1
    have ri : tags i.val=some a := (Option.some_get i.property.1).symm
    let oc : Occupied tags a:=⟨i.val,ri⟩
    apply Fin.ext
    change (first tags a oc).val=i.val.val
    apply Nat.le_antisymm (first_le tags a oc i.val ri)
    apply Nat.le_of_not_gt
    intro earlier
    exact ((no_prior tags h i.val).1 i.property).2 (first tags a oc) earlier
      ((first_read tags a oc).trans ri.symm)
  right_inv a:=by
    apply Subtype.ext
    apply Option.some.inj
    exact (Option.some_get _).trans (first_read tags a.val a.property)

variable [Fintype A]
theorem count (h : Local tags K) :
    (∑i : Fin n,if Fresh tags K i then 1 else 0)=Fintype.card {a //Occupied tags a} := by
  rw [←Fintype.card_congr (representatives tags h)]
  simp [Fintype.card_subtype,Finset.sum_boole]

omit [DecidableEq A] [Fintype A] in
theorem local_of_rows {S K : ℕ} (site : A→Fin S) (row : Fin n→Fin S) (offset : Fin n→Fin (K+1))
    (index : ∀i,i.val=(row i).val*(K+1)+(offset i).val)
    (fits : ∀i a,tags i=some a→ row i=site a) : Local tags K := by
  intro i j _ eqn active
  cases hi : tags i with
  | none=>simp [hi] at active
  | some a=>
    have e : row i=row j := (fits i a hi).trans (fits j a (eqn.symm.trans hi)).symm
    rw [index i,index j,e]
    have :=(offset i).isLt
    omega

end
end Hierarchy.DescentDistinctWindow

end OAI
