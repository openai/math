import OAI.Hierarchy.DescentResetFreshWires
import OAI.Hierarchy.DescentBundleWorld
import OAI.Hierarchy.DescentReachedPublicPointer

namespace OAI
/-! # Cable operands through the actual split and final names of a reset -/
namespace Hierarchy.DescentResetFreshWires
open DescentSixParty DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder
open DescentCompiler Computability.BorderVNP.Crossing ThreeFlat.Routing
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {p R : ℕ} {W : MarkedWorld F d P bits}
    {B : BitDescription W} (sh : WorldShape p R B)

def nodeWires (y : NodeOrder.All B) : Prop :=
  OnlyWires (N:=W.graph) (v:=y.1) (sh.sites y.1) y.2

theorem piece_wires (m : W.graph.Edge→ℕ) (q : ℕ) (cut : ∀e∈W.core,W.graph.width e=m e*q)
    (hp : 0<p) (hq : 0<q) (unit : p∣q) (v : W.graph.Site) (u : (B.recipe v).Node)
    (all : nodeWires sh ⟨v,u⟩) :
    nodeWires (sh.pieces m q cut hp hq unit) ⟨v,u⟩ :=by
  let t:=q/p
  have eqt : q=t*p:=(Nat.div_mul_cancel unit).symm
  have ht : 0<t := Nat.div_pos (Nat.le_of_dvd hq unit) hp
  let map:=pieceMap W.graph W.core m q cut hp ht eqt v
  intro j g i
  change IsWire (N:=(W.pieces q m cut).graph) v (Sum.map map.map id (((sh.sites v).chunk u j g).get i))
  obtain ⟨ref,e,read,face⟩:=all j g i
  obtain ⟨port,num,fit⟩:=ref
  dsimp only at face
  subst port
  let a : BlockRef p (boundaryWidth W.graph v):=⟨.inl e,num,fit⟩
  have dest:=congrArg Sigma.fst (map.read a ⟨0,hp⟩)
  change (map.map a).port=(pieceBit W.graph W.core m q cut v (a.atBit ⟨0,hp⟩)).1 at dest
  have found : ∃e', (map.map a).port=.inl e' :=by
    rw [dest]
    by_cases positive : e.val∈W.core <;> simp [pieceBit,BlockRef.atBit,a,positive]
  obtain ⟨child,isChild⟩:=found
  exact ⟨map.map a,child,congrArg (Sum.map map.map id) read,isChild⟩

theorem named_wires (s : Equiv.Perm W.graph.Site) (e : Equiv.Perm W.graph.Edge)
    (v : W.graph.Site) (u : (B.recipe (s.symm v)).Node) (all : nodeWires sh ⟨s.symm v,u⟩) :
    nodeWires (sh.renamed s e) ⟨v,u⟩ :=by
  intro j g i
  obtain ⟨ref,wire,read,face⟩:=all j g i
  change IsWire (N:=PhysicalRename.graph W.graph s e) v (Sum.map (namedMap W s e v).map id (((sh.sites (s.symm v)).chunk u j g).get i))
  rw [read,Sum.map_inl]
  exact ⟨_,PhysicalRename.incident W.graph s e v wire,rfl,congrArg (PhysicalRename.boundary W.graph s e v) face⟩

section Pointer
variable {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist : ℕ}
    (cap : Reached W G q ε S k age grain degree wire hist) (rank : Local B) (hp : 0<p) (pin : P→ℕ)

theorem original_cable (args : ℕ) (v : W.graph.Site) (node : (B.recipe v).Node)
    (all : nodeWires sh ⟨v,node⟩) (j : Fin ((sh.sites v).keys node).length) :
    ∃(e : Incident W.graph v) (chunk : ℕ) (fit : (chunk+1)*p≤W.graph.width e.val),
      Reached.argumentPointer cap B rank sh hp pin args ⟨v,node⟩ j.val=Reached.firstCable cap hp v e chunk fit :=by
  obtain ⟨ref,e,word,head⟩:=flat_wire all j
  have entry:= (List.getElem?_eq_getElem j.isLt).trans (congrArg some word)
  have actual:=Reached.argument_public cap hp pin B rank sh args v node j.val ref entry
  rcases ref with ⟨port,chunk,fit⟩
  dsimp only at head
  subst port
  exact ⟨e,chunk,fit,actual⟩
end Pointer
end
end Hierarchy.DescentResetFreshWires

end OAI
