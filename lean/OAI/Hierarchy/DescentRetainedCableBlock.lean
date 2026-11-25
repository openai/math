import OAI.Hierarchy.DescentOperandResetPublic
import OAI.Hierarchy.DescentNamedPublicBlock
import OAI.Hierarchy.DescentResetPrimitiveWords

namespace OAI
/-! The complete old cable operand through the grain cut and retained installation. -/
namespace Hierarchy.DescentRetainedCableBlock
open Computability.BorderVNP.Crossing DescentKernelHistory DescentBundleHistory DescentSixParty DescentResetTrunks
open DescentResetAttachments DescentRouterBank DescentOrderedWords DescentNamedContact DescentResetPointerFields
open scoped Classical
noncomputable section
set_option quotPrecheck false
open private coarse from OAI.Hierarchy.DescentBundleSplit
variable {F P : Type} [Field F] {n p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F n P bits}
    {B : BitDescription W}

/-- The argument is an actual occupied block of this precise incident edge. -/
def AtCable (s : WorldShape p R B) (hp : 0<p) (x : NodeOrder.All B) (j : ℕ) (edge : W.graph.Edge) (chunk : ℕ) : Prop :=
  ∃(k : Fin (((s.sites x.1).recipe hp).arity x.2)) (ref : BlockRef p (boundaryWidth W.graph x.1)),
    k.val=j ∧ ((s.sites x.1).recipe hp).operand x.2 k=.inl ref ∧ ref.cableNumber W.graph x.1=some (edge,chunk)

theorem cable_read {s : WorldShape p R B} {hp : 0<p} {x : NodeOrder.All B} {j chunk : ℕ}
    {edge : W.graph.Edge} (hit : AtCable s hp x j edge chunk) :
    ∃(k : Fin (((s.sites x.1).recipe hp).arity x.2)) (e : Incident W.graph x.1)
      (full : (chunk+1)*p≤W.graph.width e.val), k.val=j ∧ e.val=edge ∧
        ((s.sites x.1).recipe hp).operand x.2 k=.inl ⟨.inl e,chunk,full⟩ :=by
  obtain ⟨k,⟨e|pin,b,bound⟩,idx,read,code⟩:=hit
  · obtain ⟨rfl,rfl⟩:=Prod.mk.inj (Option.some.inj code)
    exact ⟨k,e,bound,idx,rfl,read⟩
  · cases code

variable (s : WorldShape p R B) (hp : 0<p)
theorem granular (m : W.graph.Edge→ℕ) (q : ℕ) (cut : ∀e,W.graph.width e=m e*q)
    (pos : 0<q) (unit : p∣q) (y : NodeOrder.All B) (j : ℕ) (edge : W.graph.Edge) (chunk : ℕ)
    (hit : AtCable s hp y j edge chunk) :
    ∃i : Fin (m edge),i.val=chunk/(q/p) ∧
      AtCable (s.granular m q cut hp pos unit) hp y j ⟨edge,i⟩ (chunk%(q/p)):=by
  obtain ⟨k,e,full,idx,rfl,read⟩:=cable_read hit
  have scale:q=q/p*p:=(Nat.div_mul_cancel unit).symm
  have count:0<q/p:=Nat.div_pos (Nat.le_of_dvd pos unit) hp
  let map:=grainMap W m q cut hp count scale y.1
  let src : BlockRef p (boundaryWidth W.graph y.1):=⟨.inl e,chunk,full⟩
  let part := coarse hp count scale (cut e.val) chunk full
  refine ⟨part,rfl, k.cast (rerouteLen hp (s.sites y.1) map y.2).symm,map.map src,idx,?_,rfl⟩
  exact (reroute_operand hp _ map _ k).trans (congrArg (Sum.map map.map id) read)

section Installed
variable {H Q Y : Type} [Fintype H] [Fintype Q] {L d : ℕ}
    (one : 1≤R) (home : W.graph.Site→H) (grp : Bool→W.graph.Edge→Q) (flag : H→Bool)
    {w : W.graph.Edge→ℕ} (same : w=W.graph.width) (board : Network d (Bool×Q) (publicWidth grp w))
    (legacy sorted : board.Tables F) (ids : W.graph.Edge↪Fin L) (scalar : Y→List (List Bool)→F)
    (prog : SiteBits (U:=Y) board) (valid : ReadsBits board scalar prog sorted)
    (dev : ∀v,Shape p (prog v)) (bound : ∀v u j g,((dev v).chunk u j g).stride≤R)
    (widths : ∀e,p∣board.width e)
local notation "names_" => NodeOrder.installedNames B home grp flag same board legacy sorted ids scalar prog valid
local notation "bank_" => installedWorldShape s hp one home grp flag same board legacy sorted ids scalar prog valid dev bound widths
local notation "wires_" => installedWireNames W home grp flag same board legacy
local notation "land_" => moved W.graph home

def incomingPrefix (e : W.graph.Edge) :=
  offset (DescentOrderedReset.fibreKey ids land_ (land_ e)) (fun a=>W.graph.width a.val) ⟨e,rfl⟩

omit [Field F] [Fintype H] in
private theorem prefix_at (e : W.graph.Edge) (h : H) (atHome : land_ e=h) :
    offset (DescentOrderedReset.fibreKey ids land_ h) (fun a=>W.graph.width a.val) ⟨e,atHome⟩=
      incomingPrefix home ids e:=by cases atHome;rfl

omit [Fintype Q] in
theorem installed (x : NodeOrder.All (B.installed home grp flag same board legacy sorted ids scalar prog valid))
    (y : NodeOrder.All B) (origin : names_ x=.inl y)
    (j : ℕ) (edge : W.graph.Edge) (chunk : ℕ) (hit : AtCable s hp y j edge chunk) :
    let side:=decide (W.graph.src edge≠y.1)
    AtCable bank_ hp x j ((wires_).symm (if side then .inr (.inl (land_ edge)) else .inl (false,edge)))
      ((if side then incomingPrefix home ids edge/p else 0)+chunk):=by
  subst w
  rcases x with ⟨(⟨side,h⟩|v),u⟩
  · cases side with
    | true => cases origin
    | false =>
      rcases u with ⟨⟨v,rfl⟩,u⟩
      change Sum.inl (⟨v,u⟩ : NodeOrder.All B)=_ at origin
      cases (Sum.inl.inj origin)
      obtain ⟨k,e,full,idx,rfl,read⟩:=cable_read hit
      let prior : BlockRef p (boundaryWidth W.graph v):=⟨.inl e,chunk,full⟩
      let out:=oldField hp W.graph home grp board ids s.edges v prior
      have sameBlock : out=(oldBlockMap W.graph home grp board ids s.edges v).map prior:=firstBlock_eq hp _ _ prior
      refine ⟨k.cast (retained_terminal_arity W.graph home grp board ids s.edges hp B.recipe prog s.sites dev v u).symm,out,idx,?_,?_⟩
      · rw [sameBlock]
        exact retained_public W.graph home grp board ids s.edges hp B.recipe prog s.sites dev v u k prior read
      · let encodeWire : ((DescentResetTrunks.network W.graph home grp board).Edge⊕P)×ℕ→Option ((DescentResetTrunks.network W.graph home grp board).Edge×ℕ)
            :=fun a=>a.1.elim (fun t=>some (t,a.2)) (fun _=>none)
        have collapse:out.cableNumber _ _=encodeWire (Sum.map Subtype.val Subtype.val out.port,out.block):=by
          unfold BlockRef.cableNumber
          cases out.port <;>rfl
        refine collapse.trans ?_
        by_cases head : W.graph.src e.val=v
        · rw [show (Sum.map Subtype.val Subtype.val out.port,out.block)=_ from old_at_source hp W.graph home grp board ids s.edges v e head chunk full]
          simp [head,encodeWire,installedWireNames]
          rfl
        · have dest:=e.property.resolve_left head
          rw [show (Sum.map Subtype.val Subtype.val out.port,out.block)=_ from old_at_target hp W.graph home grp board ids s.edges _ e head chunk full]
          rw [prefix_at home ids e.val (home v) (congrArg home dest)]
          simp [head,encodeWire,installedWireNames,moved,dest]
          rfl
  · cases origin

end Installed
end
end Hierarchy.DescentRetainedCableBlock

end OAI
