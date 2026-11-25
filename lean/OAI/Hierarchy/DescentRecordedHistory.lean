import OAI.Hierarchy.DescentGadgetHistory

namespace OAI
/-! # Every retained scalar in a chosen subround has a physical local contraction history -/

namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing DescentSixParty GadgetNetwork
open scoped Classical BigOperators
noncomputable section

variable {Tag Tag' B : Type} {F : Type*} [CommSemiring F]

def retag (r : Recipe Tag B) (f : Tag→Tag') : Recipe Tag' B :=
  {r with tag:=f∘r.tag}

theorem retag_value (r : Recipe Tag B) (f : Tag→Tag') (scalar : Tag'→List (List Bool)→F)
    (x : B→List Bool) : (retag r f).value scalar x=r.value (fun t=>scalar (f t)) x := rfl

section
variable {K : Type*} [Field K] (G : PoweredGadget K)
variable {I C : Type} [Fintype I] {d : ℕ} {P : Type} {bits : P→ℕ}
variable (A : World K d P bits) (pick : I×Fin 2 ↪ A.graph.Edge)
variable (z : I→ℕ) (hz : ∀i,0<z i) (fit : ∀i s,A.graph.width (pick (i,s))=z i*G.b)
variable {Z : ℕ} (room : ∀i,z i≤Z) (pack : A.graph.Site→C) (p : I→Profile G.C)
variable (old : ∀v,Recipe Tag (Boundary A.graph v))
variable (scalar : Tag →List (List Bool)→K)

local notation "S" => branchWidth G z p
local notation "M" => physical A.graph pick S
local notation "loc" => newSite A.graph pick (bestLayout S) pack
local notation "pos" => (fun _ : Merged A.graph pick (bestLayout S) pack=>(0:EuclideanSpace ℝ (Fin d)))
local notation "ball" => (fun v=> (by simp : ‖pos v‖≤1))

/-- Old atoms retain their ordinal references. Each inserted gadget vertex
adds one role atom for the truly chosen repeat count, profile, and party. -/
def physicalRecipe (v : (M).Site) : Recipe (Tag⊕GadgetTag G Z) (Boundary (M) v) :=
  match v with
  | .inl u => retag (rewire (old u) (oldBoundary A.graph pick S u)) Sum.inl
  | .inr (i,j) => retag (roleRecipe G A.graph pick z room p i j) Sum.inr

def recordedRecipe (v : (recorded G A pick z hz fit pack p).graph.Site) :
    Recipe (Tag⊕GadgetTag G Z) (Boundary (recorded G A pick z hz fit pack p).graph v) :=
  quotientRecipe (M) loc pos ball (physicalRecipe G A pick z room p old) v

theorem recorded_represents (previous : Represents A.graph scalar A.tables old) :
    Represents (recorded G A pick z hz fit pack p).graph (Sum.elim scalar (gadgetScalar G))
      (recorded G A pick z hz fit pack p).tables (recordedRecipe G A pick z hz fit room pack p old) := by
  apply quotient_represents
  intro v
  cases v with
  | inl u =>
    intro read pins
    rw [physicalRecipe,retag_value,rewire_value,old_input]
    exact previous u _ _
  | inr q =>
    intro read pins
    rw [physicalRecipe,retag_value]
    exact role_read G A.graph pick z hz fit room p q.1 q.2 read pins

theorem recorded_atoms (v : (recorded G A pick z hz fit pack p).graph.Site) :
    Fintype.card (recordedRecipe G A pick z hz fit room pack p old v).Node=
      ∑u : {u : (M).Site // loc u=v},match u.val with
        | .inl s=>Fintype.card (old s).Node
        | .inr _=>1 := by
  refine (quotient_atoms (M) loc pos ball (physicalRecipe G A pick z room p old) v).trans ?_
  apply Finset.sum_congr rfl
  rintro ⟨v,_⟩ _
  cases v with
  | inl s => exact @Fintype.card_congr _ _ _ _ (Equiv.refl (old s).Node)
  | inr q => exact @Fintype.card_unique Unit inferInstance _

end
end
end Hierarchy.DescentKernelHistory

end OAI
