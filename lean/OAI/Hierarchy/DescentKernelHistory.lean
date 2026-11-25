import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace OAI
/-! # The advice interpreter for a finite local contraction history -/

namespace Hierarchy.DescentKernelHistory
open scoped BigOperators Classical
noncomputable section

abbrev Word (n : ℕ) := Fin n→Bool
def wordList {n : ℕ} (w : Word n) := List.ofFn w

/-- Atom names and operand positions are the description. Field values live
in one immutable dictionary, shared across all sites and all occurrences. -/
structure Recipe (Tag Boundary : Type) where
  Hidden : Type
  [hiddenFinite : Fintype Hidden]
  width : Hidden→ℕ
  Node : Type
  [nodeFinite : Fintype Node]
  tag : Node→Tag
  arity : Node→ℕ
  operand : (u : Node)→Fin (arity u)→Boundary⊕Hidden

attribute [instance] Recipe.hiddenFinite Recipe.nodeFinite

variable {Tag B : Type} {F : Type*} [CommSemiring F]
variable (scalar : Tag → List (List Bool) → F)

def Recipe.value (r : Recipe Tag B) (x : B→List Bool) : F :=
  ∑h : (i : r.Hidden)→Word (r.width i), ∏v : r.Node,scalar (r.tag v)
    (List.ofFn fun j=>(r.operand v j).elim x (fun i=>wordList (h i)))

def atom (t : Tag) (n : ℕ) (args : Fin n→B) : Recipe Tag B where
  Hidden := Empty
  width := Empty.elim
  Node := Unit
  tag _ := t
  arity _ := n
  operand _ j := .inl (args j)

theorem atom_value (t : Tag) (n : ℕ) (args : Fin n→B) (x : B→List Bool) :
    (atom t n args).value scalar x=scalar t (List.ofFn fun j=>x (args j)) := by
  change (∑ _ : (i : Empty)→Word (Empty.elim i),∏ _ : Unit,scalar t (List.ofFn fun j=>x (args j)))=_
  rw [Fintype.sum_unique,Fintype.prod_unique]

def rewire {C : Type} (r : Recipe Tag B) (f : B→C) : Recipe Tag C :=
  {r with operand := fun v j=>(r.operand v j).map f id}

theorem rewire_value {C : Type} (r : Recipe Tag B) (f : B→C) (x : C→List Bool) :
    (rewire r f).value scalar x=r.value scalar (x∘f) := by
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.prod_congr rfl
  intro v _
  congr 2
  funext j
  cases hq : r.operand v j <;> simp [rewire,hq]

variable {J : Type} [Fintype J] {A : J→Type} (r : ∀i,Recipe Tag (A i))
variable {H : Type} [Fintype H] (width : H→ℕ) (place : ∀i,A i→B⊕H)

abbrev CombinedHidden := H ⊕ (Σ i,(r i).Hidden)

def combinedWidth : CombinedHidden (H:=H) r→ℕ := Sum.elim width (fun p=>(r p.1).width p.2)

def combine : Recipe Tag B where
  Hidden := CombinedHidden (H:=H) r
  width := combinedWidth r width
  Node := Σ i,(r i).Node
  tag u := (r u.1).tag u.2
  arity u := (r u.1).arity u.2
  operand u j := match (r u.1).operand u.2 j with
    | .inr privateWord => .inr (.inr ⟨u.1,privateWord⟩)
    | .inl ref => (place u.1 ref).map id Sum.inl

def combinedAssignments :
    ((p : CombinedHidden (H:=H) r)→Word (combinedWidth r width p)) ≃
      ((i : H)→Word (width i)) × ((i : J)→(j : (r i).Hidden)→Word ((r i).width j)) where
  toFun h := (fun i=>h (.inl i),fun i j=>h (.inr ⟨i,j⟩))
  invFun p
    | .inl i=>p.1 i
    | .inr ⟨i,j⟩=>p.2 i j
  left_inv h := by funext t;cases t <;> rfl
  right_inv _ := rfl

/-- When vertices merge, every old internal label remains private to its own
old recipe and the newly hidden connecting labels occur exactly once. -/
theorem combine_value (x : B→List Bool) :
    (combine r width place).value scalar x=
      ∑h : (j : H)→Word (width j), ∏i,(r i).value scalar
        (fun q=>(place i q).elim x (fun j=>wordList (h j))) := by
  unfold Recipe.value
  let eval := fun h : (p : CombinedHidden (H:=H) r)→Word (combinedWidth r width p)=>
    ∏v : (combine r width place).Node,scalar ((combine r width place).tag v)
      (List.ofFn fun j=>((combine r width place).operand v j).elim x (fun i=>wordList (h i)))
  let eqv := combinedAssignments r width
  trans ∑h,eval h
  · apply Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
    intro a _
    rfl
  calc
    ∑h,eval h=∑q,eval (eqv.symm q) := (eqv.symm.sum_comp eval).symm
    _ = _ := ?_
  rw [Fintype.sum_prod_type]
  dsimp only [eval,eqv]
  apply Finset.sum_congr rfl
  intro h _
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro inner _
  rw [←Fintype.prod_sigma']
  apply Finset.prod_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
  rintro ⟨i,v⟩ _
  congr 2
  funext j
  cases entry : (r i).operand v j with
  | inl ref => cases pointer : place i ref <;> simp [combine,entry,pointer,combinedAssignments,combinedWidth]; rfl
  | inr ref => simp [combine,entry,combinedAssignments,combinedWidth]; rfl

theorem combine_nodes : Fintype.card (combine r width place).Node=∑i,Fintype.card (r i).Node :=
  Fintype.card_sigma

/-- Each old local atom's history retains its arity, so its control has exactly
as many operand references after gathering as before gathering. -/
theorem combine_operands :
    (∑v : (combine r width place).Node,(combine r width place).arity v)=
      ∑i,∑v : (r i).Node,(r i).arity v := Fintype.sum_sigma _

end
end Hierarchy.DescentKernelHistory

end OAI
