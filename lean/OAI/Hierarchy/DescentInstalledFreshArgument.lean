import OAI.Hierarchy.DescentResetTrunkInstalledKeys
import OAI.Hierarchy.DescentRetainedCableBlock
import OAI.Hierarchy.DescentResetOriginRank

namespace OAI
/-! # Named original arguments at the relay and router sites of a reset installation -/
namespace Hierarchy.DescentResetFreshWires
open DescentSixParty DescentKernelHistory DescentBundleHistory DescentOrderedWords DescentResetTrunks
open DescentRouterBank DescentResetAttachments DescentNamedContact DescentResetPointerFields
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {n p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F n P bits} {B : BitDescription W}

def keyCable (shape : WorldShape p R B) (x : NodeOrder.All B) (j : ℕ) : Option (W.graph.Edge×ℕ) :=
  ((shape.sites x.1).keys x.2)[j]?.bind (fun a=>a.elim (BlockRef.cableNumber W.graph x.1) (fun _=>none))

theorem keyCable_read (shape : WorldShape p R B) (x : NodeOrder.All B) (j : ℕ)
    (e : Incident W.graph x.1) (w : ℕ) (fit : (w+1)*p≤W.graph.width e.val)
    (issued : keyCable shape x j=some (e.val,w)) :
    ((shape.sites x.1).keys x.2)[j]?=some (.inl ⟨.inl e,w,fit⟩) :=by
  unfold keyCable at issued
  cases seen : ((shape.sites x.1).keys x.2)[j]? with
  | none=>simp [seen] at issued
  | some a=>
    rw [seen] at issued
    rcases a with ⟨a|pin,v,room⟩|priv
    · change some (a.val,v)=some (e.val,w) at issued
      obtain ⟨eqn,rfl⟩:=Prod.mk.inj (Option.some.inj issued)
      cases Subtype.ext eqn
      rfl
    · cases issued
    · cases issued

theorem keyCable_entry (shape : WorldShape p R B) (x : NodeOrder.All B) (j : ℕ)
    (edge : W.graph.Edge) (word : ℕ) (issued : keyCable shape x j=some (edge,word)) :
    ∃ (e : Incident W.graph x.1) (fit : (word+1)*p≤W.graph.width e.val), e.val=edge ∧
      ((shape.sites x.1).keys x.2)[j]?=some (.inl ⟨.inl e,word,fit⟩) :=by
  unfold keyCable at issued
  cases seen : ((shape.sites x.1).keys x.2)[j]? with
  | none=>simp [seen] at issued
  | some a=>
    rw [seen] at issued
    rcases a with ⟨e|pin,v,room⟩|priv
    · change some (e.val,v)=some (edge,word) at issued
      obtain ⟨same,rfl⟩:=Prod.mk.inj (Option.some.inj issued)
      exact ⟨e,room,same,rfl⟩
    · cases issued
    · cases issued

variable (sh : WorldShape p R B) (hp : 0<p) (one : 1≤R)
variable {H Q Y : Type} [Fintype H] [Fintype Q] {L d : ℕ}
    (home : W.graph.Site→H) (grp : Bool→W.graph.Edge→Q) (flag : H→Bool)
    {w : W.graph.Edge→ℕ} (same : w=W.graph.width) (board : Network d (Bool×Q) (publicWidth grp w))
    (legacy sorted : board.Tables F) (ids : W.graph.Edge↪Fin L) (scalar : Y→List (List Bool)→F)
    (prog : SiteBits (U:=Y) board) (valid : ReadsBits board scalar prog sorted)
    (dev : ∀v,Shape p (prog v)) (bound : ∀v u j g,((dev v).chunk u j g).stride≤R)
    (widths : ∀e,p∣board.width e)
local notation "names_" => NodeOrder.installedNames B home grp flag same board legacy sorted ids scalar prog valid
local notation "installed_" => installedWorldShape sh hp one home grp flag same board legacy sorted ids scalar prog valid dev bound widths
local notation "wire_" => installedWireNames W home grp flag same board legacy

omit [Fintype Q] in
/-- This equality uses both the original node name and the original names of the installed wires. -/
theorem installed_relay (x : NodeOrder.All (B.installed home grp flag same board legacy sorted ids scalar prog valid))
    (e : W.graph.Edge) (origin : names_ x=.inr (.inl e)) (face : Fin 2) (j : Fin (W.graph.width e/p)) :
    let h:=moved W.graph home e
    let offsetBits:=DescentRetainedCableBlock.incomingPrefix (W:=W) home ids e
    keyCable installed_ x (finProdFinEquiv (face,j)).val=
      some ((wire_).symm (if face.val=0 then .inr (.inl h) else .inl (true,e)),
        (if face.val=0 then offsetBits/p else 0)+j.val) :=by
  obtain ⟨a₀,rfl⟩:=(names_).symm.surjective x
  rw [Equiv.apply_symm_apply] at origin
  subst a₀
  subst w
  let h:=moved W.graph home e
  let item:Fibre (moved W.graph home) h:=⟨e,rfl⟩
  let r:=relayRef W.graph home grp board ids sh.edges h item face j
  change ((trunkShape W.graph home grp board ids sh.edges hp B.recipe prog sh.sites dev
    (.inl (true,h))).keys item)[(finProdFinEquiv (face,j)).val]?.bind _=_
  rw [relay_key_at]
  change r.cableNumber _ _=_
  by_cases zero : face.val=0
  · simp [r,relayRef,zero,BlockRef.cableNumber,inside,DescentRetainedCableBlock.incomingPrefix,
      installedWireNames,h,item]
    rfl
  · simp [r,relayRef,zero,BlockRef.cableNumber,installedWireNames]
    rfl

omit [Fintype Q] in
/-- On either router family the original named bank edge is embedded once and keeps its word index. -/
theorem installed_device_wire (x : NodeOrder.All (B.installed home grp flag same board legacy sorted ids scalar prog valid))
    (v : board.Site) (u : (prog v).Node) (origin : names_ x=.inr (.inr ⟨v,u⟩))
    (j a : ℕ) (e : Incident board v) (fit : (a+1)*p≤board.width e.val)
    (read : ((dev v).keys u)[j]?=some (.inl ⟨.inl e,a,fit⟩)) :
    keyCable installed_ x j=some ((wire_).symm (.inr (.inr e.val)),a) :=by
  obtain ⟨a₀,rfl⟩:=(names_).symm.surjective x
  rw [Equiv.apply_symm_apply] at origin
  subst a₀
  subst w
  let edge : Incident (network W.graph home grp board) (.inr v):=⟨.inr (.inr e.val),by
    rcases e.property with h|h
    · exact Or.inl (congrArg Sum.inr h)
    · exact Or.inr (congrArg Sum.inr h)⟩
  change ((trunkShape W.graph home grp board ids sh.edges hp B.recipe prog sh.sites dev (.inr v)).keys u)[j]?.bind _=_
  rw [device_wire_at W.graph home grp board ids sh.edges hp B.recipe prog sh.sites dev v u j e a fit read edge rfl fit]
  rfl

omit [Fintype Q] in
/-- At an attached pin, the first bit of the word selects the old signed grain by
the authentic ordered concatenation of the socket's original edge fibre. -/
theorem installed_device_socket (x : NodeOrder.All (B.installed home grp flag same board legacy sorted ids scalar prog valid))
    (v : board.Site) (u : (prog v).Node) (origin : names_ x=.inr (.inr ⟨v,u⟩))
    (j a : ℕ) (pin : Attached board v) (fit : (a+1)*p≤publicWidth grp w pin.val)
    (read : ((dev v).keys u)[j]?=some (.inl ⟨.inr pin,a,fit⟩)) :
    let order:=DescentOrderedReset.fibreKey ids (grp pin.val.1) pin.val.2
    let widths₀:=fun e : Fibre (grp pin.val.1) pin.val.2=>w e.val
    let r : BlockRef p (boundaryWidth board v):=⟨.inr pin,a,fit⟩
    let selected:=(address order widths₀).symm (r.atBit ⟨0,hp⟩).2
    keyCable installed_ x j=some ((wire_).symm (.inl (pin.val.1,selected.1.val)),selected.2.val/p) :=by
  obtain ⟨a₀,rfl⟩:=(names_).symm.surjective x
  rw [Equiv.apply_symm_apply] at origin
  subst a₀
  subst w
  let r : BlockRef p (boundaryWidth board v):=⟨.inr pin,a,fit⟩
  let file:=bankField hp W.graph home grp board ids sh.edges v r
  change ((trunkShape W.graph home grp board ids sh.edges hp B.recipe prog sh.sites dev (.inr v)).keys u)[j]?.bind _=_
  rw [device_key_at W.graph home grp board ids sh.edges hp B.recipe prog sh.sites dev v u j r read]
  change file.cableNumber _ _=_
  let code : ((network W.graph home grp board).Edge⊕P)×ℕ→Option ((network W.graph home grp board).Edge×ℕ)
    :=fun z=>z.1.elim (fun t=>some (t,z.2)) (fun _=>none)
  have restore : file.cableNumber _ _=code (file.port.map Subtype.val Subtype.val,file.block):=by
    unfold BlockRef.cableNumber
    cases file.port <;>rfl
  rw [restore,show (file.port.map Subtype.val Subtype.val,file.block)=_ from
    bank_at_pin hp W.graph home grp board ids sh.edges v pin a fit]
  rfl

end
end Hierarchy.DescentResetFreshWires

end OAI
