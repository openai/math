import OAI.Hierarchy.DescentResetGateCalls
import OAI.Hierarchy.DescentRecipeFootprint
import OAI.Hierarchy.DescentBoundedBitHistory

namespace OAI
/-! # Bit-addressed scalar requests on finite physical boundary ports -/

namespace Hierarchy.DescentResetGates
open Computability.BorderVNP.Crossing DescentKernelHistory
open scoped Classical BigOperators
noncomputable section
variable {A B Key : Type} {width : A→ℕ} {newWidth : B→ℕ}

structure Gather (Key A : Type) (width : A→ℕ) where
  Port : Type
  [finite : Fintype Port]
  size : Port→ℕ
  ref : (p : Port)→Fin (size p)→BitRef width
  decode : ((p : Port)→Word (size p))→Request Key
attribute [instance] Gather.finite

def Gather.observe (g : Gather Key A width) (read : BitRef width→Bool) := g.decode (fun p j=>read (g.ref p j))

def Gather.reroute (g : Gather Key A width) (f : BitRef width→BitRef newWidth) : Gather Key B newWidth :=
  {g with ref := fun p j=>f (g.ref p j)}

def Gather.positions (g : Gather Key A width) : g.Port ≃ Fin (Fintype.card g.Port) := Fintype.equivFin _

def Gather.arguments (g : Gather Key A width) (x : List (List Bool)) := g.decode (fun p j=>
  (x.getD (g.positions p).val []).getD j.val false)

theorem Gather.arguments_read (g : Gather Key A width) (read : BitRef width→Bool) :
    g.arguments (List.ofFn (fun j=>wordList (fun t=>read (g.ref (g.positions.symm j) t))))=g.observe read := by
  unfold arguments observe
  apply congrArg g.decode
  funext p j
  let row (q : g.Port) : List Bool := wordList (fun t => read (g.ref q t))
  let rows (i : Fin (Fintype.card g.Port)) := row (g.positions.symm i)
  change ((List.ofFn rows).getD (g.positions p).val []).getD j.val false = _
  have atPort : (List.ofFn rows).getD (g.positions p).val [] = rows (g.positions p) := by simp
  have sameRow : rows (g.positions p) = row p := congrArg row (g.positions.symm_apply_apply p)
  rw [atPort, sameRow]
  simp [row, wordList]

variable {D d : ℕ} {P K : Type} {bits : P→ℕ} [CommSemiring K] {N : Network D P bits} (S : Calls N Key)

def siteBit {v : N.Site} (read : ∀e:Incident N v,Word (N.width e.val)) (pin : ∀p:Attached N v,Word (bits p.val)) :
    BitRef (boundaryWidth N v)→Bool
  | ⟨.inl e,j⟩=>read e j
  | ⟨.inr p,j⟩=>pin p j

def allBoundary [Fintype P] (v : N.Site) (i : S.Gate v) : Gather Key (Boundary N v) (boundaryWidth N v) where
  Port := Boundary N v
  size := boundaryWidth N v
  ref p j := ⟨p,j⟩
  decode t := S.bitRequest v i (fun e=>t (.inl e)) (fun p=>t (.inr p))

variable (g : ∀ v (_i : S.Gate v),Gather Key (Boundary N v) (boundaryWidth N v))

def bitRecipe (v : N.Site) : BitRecipe S.Tag (Boundary N v) (boundaryWidth N v) where
  Hidden := Empty
  hiddenWidth := Empty.elim
  Node := S.Gate v
  tag i := ⟨v,i⟩
  arity i := Fintype.card (g v i).Port
  size i j := (g v i).size ((g v i).positions.symm j)
  arg i j t := .inl ((g v i).ref ((g v i).positions.symm j) t)

def bitScalar (rom : Key→K) (t : S.Tag) (args : List (List Bool)) : K := ((g t.1 t.2).arguments args).value rom

theorem bitRecipe_nodeBits (v : N.Site) (i : S.Gate v) :
    (bitRecipe S g v).nodeBits i=∑p,(g v i).size p := (g v i).positions.symm.sum_comp _

theorem bitRecipe_read (rom : Key→K) (v : N.Site) (read : BitRef (boundaryWidth N v)→Bool) :
    (bitRecipe S g v).value (bitScalar S g rom) read=∏i,((g v i).observe read).value rom := by
  change (∑_h : (i : Empty)→Word (Empty.elim i),∏i : S.Gate v,((g v i).arguments
    (List.ofFn (fun j=>wordList (fun t=>read ((g v i).ref ((g v i).positions.symm j) t))))).value rom)=_
  simp [Gather.arguments_read]

open private DescentNetworkSubstitution.sourceTap_at DescentNetworkSubstitution.targetTap_at DescentNetworkSubstitution.pinTap_at from OAI.Hierarchy.DescentNetworkSubstitution
variable (N) (M : ∀v,Network d (DescentNetworkSubstitution.Slot N v) (DescentNetworkSubstitution.slotWidth N v))
local notation "Q" => DescentNetworkSubstitution.network N M

/-- Every bit of an inner device is either carried by its own private cable, by a real old joining cable,
or by the corresponding original exterior pin of the complete substituted graph. -/
def substituteBit (v : N.Site) (j : (M v).Site) : BitRef (boundaryWidth (M v) j)→BitRef (boundaryWidth Q ⟨v,j⟩)
  | ⟨.inl e,k⟩=>⟨.inl ⟨.inr ⟨v,e.val⟩, e.property.imp (congrArg (Sigma.mk v)) (congrArg (Sigma.mk v))⟩,k⟩
  | ⟨.inr ⟨.inl e,h⟩,k⟩=>⟨.inl ⟨.inl e.val,Or.inl ((DescentNetworkSubstitution.sourceTap_at N M e).trans (congrArg (Sigma.mk v) h))⟩,k⟩
  | ⟨.inr ⟨.inr (.inl e),h⟩,k⟩=>⟨.inl ⟨.inl e.val,Or.inr ((DescentNetworkSubstitution.targetTap_at N M e).trans (congrArg (Sigma.mk v) h))⟩,k⟩
  | ⟨.inr ⟨.inr (.inr p),h⟩,k⟩=>⟨.inr ⟨p.val,(DescentNetworkSubstitution.pinTap_at N M p).trans (congrArg (Sigma.mk v) h)⟩,k⟩

def assignmentBit (N : Network D P bits) (a : N.Assignment) (x : Ports bits) (v : N.Site) : BitRef (boundaryWidth N v)→Bool :=
  siteBit (fun e=>a e.val) (fun p=>x p.val)

theorem substituteBit_read (a : (Q).Assignment) (x : Ports bits) (v : N.Site) (j : (M v).Site) (b : BitRef (boundaryWidth (M v) j)) :
    assignmentBit Q a x ⟨v,j⟩ (substituteBit N M v j b)=
    assignmentBit (M v) ((DescentNetworkSubstitution.assignmentEquiv N M a).2 v)
      (DescentNetworkSubstitution.visible N (DescentNetworkSubstitution.assignmentEquiv N M a).1 x v) j b := by
  rcases b with ⟨e|p,k⟩
  · rfl
  · rcases p with ⟨e|(e|p),h⟩ <;> rfl

end
end Hierarchy.DescentResetGates

end OAI
