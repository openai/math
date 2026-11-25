import OAI.Hierarchy.DescentOrdinaryNodeOrder

namespace OAI
/-! # Operand and bit-reference readback at actual ordinary scalar nodes -/

namespace Hierarchy.DescentKernelHistory.NodeOrder
open Computability.BorderVNP.Crossing DescentSixParty GadgetNetwork DescentNetworkPartition
open scoped Classical
noncomputable section

variable {F U P C : Type} [Field F] [Fintype C] {D d : ℕ} {bits : P→ℕ}
variable (N : Network D P bits) (loc : N.Site→C) (pos : C→EuclideanSpace ℝ (Fin d))
    (ball : ∀v,‖pos v‖≤1) (r : SiteBits (U:=U) N)

local notation "Q" => quotient N loc pos ball

/-- A previously private word keeps its old owner; a newly private cable
uses the actual interior-cable constructor. All other bits use their
surviving public endpoint. These are the two branches of the quotient's
actual hidden-word dictionary. -/
def quotientRef (v : C) (s : {u // loc u=v}) :
    BitRef (boundaryWidth N s.val) ⊕ BitRef (r s.val).hiddenWidth →
      BitRef (boundaryWidth (Q) v) ⊕ BitRef (quotientBits N loc pos ball r v).hiddenWidth
  | .inr ⟨e,t⟩=>.inr ⟨.inr ⟨s,e⟩,t⟩
  | .inl e=>match quotientBit N loc pos ball v s e with
    | .inl a=>.inl a
    | .inr ⟨e,t⟩=>.inr ⟨.inl e,t⟩

theorem quotient_arg (v : C) (s : {u //loc u=v}) (a : (r s.val).Node)
    (j : Fin ((r s.val).arity a)) (t : Fin ((r s.val).size a j)) :
    (quotientBits N loc pos ball r v).arg ⟨s,a⟩ j t=
      quotientRef N loc pos ball r v s ((r s.val).arg a j t) := by
  cases arg : (r s.val).arg a j t with
  | inl e =>
    cases target : quotientBit N loc pos ball v s e with
    | inl dest => simp only [quotientBits,BitRecipe.combineBits,quotientRef,arg,target]
    | inr hidden =>
      rcases hidden with ⟨wire,bit⟩
      simp only [quotientBits,BitRecipe.combineBits,quotientRef,arg,target]
  | inr hidden =>
    rcases hidden with ⟨wire,bit⟩
    simp only [quotientBits,BitRecipe.combineBits,quotientRef,arg]

variable {W : MarkedWorld F d P bits} (B : BitDescription W)
variable {I V : Type} [Fintype I] (G : PoweredGadget F) (pick : I×Fin 2 ↪ W.graph.Edge)
variable (z : I→ℕ) (hz : ∀i,0<z i) (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b)
variable {Z : ℕ} (room : ∀i,z i≤Z) (pack : W.graph.Site→V) (p : I→Profile G.C)
local notation "chosen" => B.selected G pick z hz fit room pack p
local notation "supply" => branchWidth G z p
local notation "M" => physical W.graph pick supply
local notation "physicalRows" => physicalBits G W.toWorld pick z room p B.recipe
local notation "dest" => newSite W.graph pick (bestLayout supply) pack
local notation "names" => selectedNames B G pick z hz fit room pack p
local notation "route" => quotientRef (d:=d) (M) dest (fun _=>0) (fun _=>by simp) physicalRows

theorem carried_arity (v : W.graph.Site) (a : (B.recipe v).Node) :
    let x:=(names).symm (.inl ⟨v,a⟩)
    ((chosen).recipe x.1).arity x.2=(B.recipe v).arity a := rfl

theorem carried_size (v : W.graph.Site) (a : (B.recipe v).Node) (j : Fin ((B.recipe v).arity a)) :
    let x:=(names).symm (.inl ⟨v,a⟩)
    ((chosen).recipe x.1).size x.2 j=(B.recipe v).size a j := rfl

/-- The row of an inherited scalar reuses the particular old operand and
bit index. At a public operand it first applies the physical cable/arm
rerouting, then decides interior versus surviving by the real venue map. -/
theorem carried_arg (v : W.graph.Site) (a : (B.recipe v).Node)
    (j : Fin ((B.recipe v).arity a)) (t : Fin ((B.recipe v).size a j)) :
    let x:=(names).symm (.inl ⟨v,a⟩)
    ((chosen).recipe x.1).arg x.2 j t=
      route (dest (.inl v)) ⟨.inl v,rfl⟩
        (((B.recipe v).arg a j t).map (carriedBit G W.toWorld pick z p v) id) := by
  exact quotient_arg (d:=d) (M) dest (fun _=>0) (fun _=>by simp) physicalRows
    (dest (.inl v)) ⟨.inl v,rfl⟩ a j t

theorem born_arity (i : I) (party : Fin 6) :
    let x:=(names).symm (.inr (i,party))
    ((chosen).recipe x.1).arity x.2=Fintype.card (RolePort party) := rfl

theorem born_size (i : I) (party : Fin 6) (j : Fin (Fintype.card (RolePort party))) :
    let x:=(names).symm (.inr (i,party))
    ((chosen).recipe x.1).size x.2 j=
      boundaryWidth (M) (.inr (i,party)) (nativeRole W.graph pick supply i party ((roleIndex party).symm j)) := rfl

/-- Every born operand names its actual demand/supply role in the installed
six-party graph. Its bit then traverses the same quotient selector as a
carried operand, with the original within-word bit index. -/
theorem born_arg (i : I) (party : Fin 6) (j : Fin (Fintype.card (RolePort party)))
    (t : Fin (boundaryWidth (M) (.inr (i,party)) (nativeRole W.graph pick supply i party ((roleIndex party).symm j)))) :
    let x:=(names).symm (.inr (i,party))
    ((chosen).recipe x.1).arg x.2 j t =
      route (dest (.inr (i,party))) ⟨.inr (i,party),rfl⟩
        (.inl ⟨nativeRole W.graph pick supply i party ((roleIndex party).symm j),t⟩) := by
  exact quotient_arg (d:=d) (M) dest (fun _=>0) (fun _=>by simp) physicalRows
    (dest (.inr (i,party))) ⟨.inr (i,party),rfl⟩ () j t

end
end Hierarchy.DescentKernelHistory.NodeOrder

end OAI
