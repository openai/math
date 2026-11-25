import OAI.Hierarchy.DescentKernelHistory
import OAI.Hierarchy.DescentNetworkPartition

namespace OAI
/-! # Operand-preserving history compilation for a real quotient site -/

namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing DescentNetworkPartition
open scoped BigOperators Classical
noncomputable section
variable {D d : ℕ} {P : Type} {bits : P→ℕ} (N : Network D P bits)
abbrev Incident (v : N.Site) := {e : N.Edge // N.src e=v ∨ N.dst e=v}
abbrev Attached (v : N.Site) := {p : P // N.attach p=v}
abbrev Boundary (v : N.Site) := Incident N v ⊕ Attached N v
def input {v : N.Site} (read : ∀e : Incident N v,Word (N.width e.1))
    (pins : ∀p : Attached N v,Word (bits p.1)) : Boundary N v → List Bool :=
  Sum.elim (fun e=>wordList (read e)) (fun p=>wordList (pins p))

variable {Tag : Type} {F : Type*} [CommSemiring F] (scalar : Tag→List (List Bool)→F)
def Represents (T : N.Tables F) (r : ∀v,Recipe Tag (Boundary N v)) :=
  ∀v read pins,(r v).value scalar (input N read pins)=T v read pins

variable {C : Type} [Fintype C] (loc : N.Site→C)
variable (pos : C→EuclideanSpace ℝ (Fin d)) (hpos : ∀c,‖pos c‖≤1)
local notation "Q" => quotient N loc pos hpos

def quotientRef (c : C) (v : {u // loc u=c}) :
    Boundary N v.val → Boundary (Q) c ⊕ PrivateEdge N loc c
  | .inr p => .inl (.inr ⟨p.val,(congrArg loc p.property).trans v.property⟩)
  | .inl e =>
    let h := e.property.imp (fun eq=>(congrArg loc eq).trans v.property)
      (fun eq=>(congrArg loc eq).trans v.property)
    if privateCable : loc (N.src e.val)=loc (N.dst e.val) then
      .inr ⟨e.val,h.elim (fun hs=>⟨hs,privateCable.symm.trans hs⟩) (fun ht=>⟨privateCable.trans ht,ht⟩)⟩
    else .inl (.inl ⟨⟨e.val,privateCable⟩,h⟩)

def quotientRecipe (r : ∀v,Recipe Tag (Boundary N v)) (c : C) : Recipe Tag (Boundary (Q) c) :=
  combine (fun v : {u // loc u=c}=>r v.1) (fun e : PrivateEdge N loc c=>N.width e.1)
    (quotientRef N loc pos hpos c)

theorem quotient_represents (T : N.Tables F) (r : ∀v,Recipe Tag (Boundary N v))
    (ok : Represents N scalar T r) :
    Represents (Q) scalar (tables N loc pos hpos T) (quotientRecipe N loc pos hpos r) := by
  intro c read pins
  rw [quotientRecipe,combine_value]
  unfold tables
  apply Finset.sum_congr (by ext x;simp only [Finset.mem_univ])
  intro hidden _
  apply Finset.prod_congr rfl
  intro v _
  rw [←ok v.val]
  congr 1
  funext p
  cases p with
  | inr p => rfl
  | inl e =>
    by_cases priv : loc (N.src e.val)=loc (N.dst e.val) <;> simp [input,quotientRef,localWord,priv]

theorem quotient_atoms (r : ∀v,Recipe Tag (Boundary N v)) (c : C) :
    Fintype.card (quotientRecipe N loc pos hpos r c).Node=∑v : {u // loc u=c},Fintype.card (r v.1).Node :=
  Fintype.card_sigma

end
end Hierarchy.DescentKernelHistory

end OAI
