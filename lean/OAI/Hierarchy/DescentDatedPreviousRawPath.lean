import OAI.Hierarchy.DescentDatedRawDonorMembership
import OAI.Hierarchy.DescentDatedOperandCommonPath

namespace OAI
/-! # One authenticated receiver ordinal for the retained signed source and the raw material endpoint -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentSixParty DescentStageEdgeReceipt DescentRawCablePanel DescentSharedCableNames
open DescentHostDirectory DescentCableDonorNames DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a H Z w M : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i) (groups : J≃Fin Z) (hosts : V↪Fin H) (win : J×V→Fin (2^k)→Cell a)
    (he : 0≤ε) (hm : 0<M) (profile dest : ℕ) (m : Memory w) (hub : V→Bool) (lay : Bool) (bytes slots : ℕ)
local notation "rank" => groupRank (groups.toEmbedding.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "near" => hostRotor hosts (DescentGroupPeerOrder.hostRoster A (hosts.trans Fin.valEmbedding))
local notation "fmt" => shapeOf (short:=short) A bytes
local notation "scene" => nativeParts (short:=short) A native S ready rank win groups hosts hm profile dest m near hub lay bytes
local notation "physical" => physicalSigned A native S ready rank groups hosts
local notation "terrain₀" => terrain (short:=short) A native S ready (cableNames k rank) win (rotor A rank)
local notation "panel" => spread groups.toEmbedding hosts terrain₀
local notation "out" => DescentSharedCableNames.Stage.outgoing A native S ready
local notation "Positive" => DescentSharedCableNames.Stage.Positive A
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed (groupRank (groups.toEmbedding.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)))
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u,(win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2+(scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (order : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)

open DescentSixParty.StarKeys DescentPacking
local notation "N" => W.graph
local notation "traffic" => nativeTraffic N W.core home color
local notation "pick" => colorPick N W.core home color A.cap
local notation "packs" => coloredPack N W.core home color A.cap
variable (same : ∀e∈W.core,scanColorAt he A.stage (W.graph.src e)=scanColorAt he A.stage (W.graph.dst e))
local notation "own" => nativeKey N W.core home color A.cap addr same lay
local notation "venue" => newSite N pick lay packs
local notation "left" => fun (e : DescentRawCablePanel.Live A pick) => (venue (GadgetNetwork.source N e.val))
local notation "right" => fun (e : DescentRawCablePanel.Live A pick) => (venue (GadgetNetwork.target N pick e.val))
local notation "anchor_" => fun (e : DescentRawCablePanel.Live A pick) => (⟨anchor pick e.val,e.property⟩:Positive)
local notation "point" => fun (e : DescentRawCablePanel.Live A pick) => (A.pos (W.graph.src (anchor_ e).val))


local notation "WHost" => DescentSharedCableNames.Stage.Host J V k
local notation "receiver" => fun (edge : DescentRawCablePanel.Live A pick) (side : Bool) => hosts ((if side then own (right edge) else own (left edge)).1).2
local notation "oldSite" => fun (edge : DescentRawCablePanel.Live A pick) => W.graph.src (anchor_ edge).val
local notation "rawWord" => fun (edge : DescentRawCablePanel.Live A pick) (side : Bool) => DepotRAM.rawAtSeat fmt profile G.b slots side
  (scene (hosts (point edge).2) (groups (point edge).1)) (A.block (oldSite edge)) (out (anchor_ edge)) (role edge.val)
local notation "record" => DescentSharedCableNames.Stage.live A native S ready (cableNames k rank)
local notation "grain" => DescentSharedCableNames.Stage.recover A
open DescentDatedSourcePathDirectory

private theorem roster_mapped (v : J×V) (i : Fin A.degree) :
    near (hosts v.2) i=((rotor A rank) v i).map (fun t=>hosts t.2) :=by
  rcases v with ⟨j,v⟩
  have yes : ∃u,hosts u=hosts v:=⟨v,rfl⟩
  simp only [hostRotor,dite_eq_left yes,hosts.injective yes.choose_spec,DescentGroupPeerOrder.rotor_group,
    Option.map_map,Function.comp_def]

set_option maxHeartbeats 700000 in
include coord named fit winner df order in
theorem original_previous_and_raw (e : DescentRawCablePanel.Live A pick) (side : Bool)
    (h : WHost) (u : A.CellPorts h.1.1 h.1.2 h.2) (sameEdge : (grain h u).1=(anchor_ e).val)
    (p : Fin (breadth A.degree)) (actor : Gather.reaching near (receiver e side) p=some (hosts h.1.2)) :
    let r:=record h u
    let src:=hosts (point e).2
    ∃back q,rawWord e side=Packed.token (some back) ∧
      walk near src (path back) 4=some (receiver e side) ∧
      Gather.select (Gather.reaching near) (receiver e side) q=some src ∧
      value (Gather.reaching near) (receiver e side) p
        (shortPath (if r.target then r.neighbor.castSucc else Fin.last A.degree))=q.val+1 ∧
      Rebase.value near .path src back=q.val :=by
  intro r src
  obtain ⟨back,word,walk_⟩:=original_raw_walk A native S ready groups hosts win he hm profile dest m hub lay bytes slots
    coord named fit winner df order same near (fun _ _=>rfl) (roster_mapped A groups hosts)
    (reciprocal A hosts) e side
  have sourceEq : hosts (A.pos (W.graph.src (grain h u).1)).2 = src :=
    congrArg (fun v => hosts (A.pos (W.graph.src v)).2) sameEdge
  have forward : walk near (hosts (A.pos (W.graph.src (grain h u).1)).2) (path back) 4=some (receiver e side):=by
    exact (congrArg (fun v => walk near v (path back) 4) sourceEq).trans walk_
  obtain ⟨q,selected,raw,reverse⟩:=previous_source_from_raw A native S ready
    (groups.toEmbedding.trans Fin.valEmbedding) hosts h u (receiver e side) p back actor forward
  exact ⟨back,q,word,walk_,selected.trans (congrArg some sourceEq),raw,
    (congrArg (fun v => Rebase.value near .path v back) sourceEq).symm.trans reverse⟩

/-- The inherited occurrence has the same original cable on both orientations of its true stored grain. -/
def previousPortRaw (h : WHost) (u : A.CellPorts h.1.1 h.1.2 h.2) :
    DescentRawCablePanel.Live A pick :=
  ⟨.inl (grain h u).1,(Nat.zero_le _).trans_lt (grain h u).2.isLt⟩

include coord named fit winner df order in
theorem original_previous_port (side : Bool) (h : WHost) (u : A.CellPorts h.1.1 h.1.2 h.2)
    (p : Fin (breadth A.degree))
    (actor : Gather.reaching near (receiver (previousPortRaw A he h u) side) p=some (hosts h.1.2)) :
    let e:=previousPortRaw A he h u
    let r:=record h u
    let src:=hosts (point e).2
    ∃back q,rawWord e side=Packed.token (some back) ∧
      walk near src (path back) 4=some (receiver e side) ∧
      Gather.select (Gather.reaching near) (receiver e side) q=some src ∧
      value (Gather.reaching near) (receiver e side) p
        (shortPath (if r.target then r.neighbor.castSucc else Fin.last A.degree))=q.val+1 ∧
      Rebase.value near .path src back=q.val :=
  original_previous_and_raw A native S ready groups hosts win he hm profile dest m hub lay bytes slots
    coord named fit winner df order same (previousPortRaw A he h u) side h u rfl p actor

include coord named fit winner df order in
/-- A newborn actor uses its old donor's unique path at the receiving owner.
Every source-column receipt for that donor returns this same ordinal. -/
theorem original_birth_root (e : DescentRawCablePanel.Live A pick) (side : Bool) :
    let src:=hosts (point e).2
    let dst:=receiver e side
    ∃back q,rawWord e side=Packed.token (some back) ∧ walk near src (path back) 4=some dst ∧
      Gather.select (Gather.reaching near) dst q=some src ∧ Rebase.value near .path src back=q.val ∧
      ∀p,Gather.select (Gather.reaching near) dst p=some src→p=q :=by
  intro src dst
  obtain ⟨back,word,forward⟩:=original_raw_walk A native S ready groups hosts win he hm profile dest m hub lay bytes slots
    coord named fit winner df order same near (fun _ _=>rfl) (roster_mapped A groups hosts)
    (reciprocal A hosts) e side
  obtain ⟨digits,issued⟩:=reverse_path near (reciprocal A hosts) (path back) src dst forward
  have hit : ∃j,Gather.reaching near dst j=some src :=by
    exact ⟨finFunctionFinEquiv digits,by simpa only [Gather.reaching,path,Equiv.symm_apply_apply] using issued⟩
  obtain ⟨q,selected,unique⟩:=Gather.once (Gather.reaching near) dst src hit
  exact ⟨back,q,word,forward,selected,Rebase.canonical_path near src dst back q forward selected,unique⟩

set_option maxHeartbeats 700000 in
include coord named fit winner df order in
/-- At the actual owner of an inherited site, the measured old head itself selects
the unique retained actor path needed by the signed source lookup. -/
theorem previous_at_owner (e : DescentRawCablePanel.Live A pick) (side : Bool)
    (a : (N).Site) (u : A.CellPorts (A.pos a).1 (A.pos a).2 (A.block a))
    (sameEdge : (grain (DescentSharedCableNames.Stage.home A a) u).1=(anchor_ e).val)
    (atOwner : receiver e side=hosts (own (venue (.inl a))).1.2) :
    let h:=DescentSharedCableNames.Stage.home A a
    let r:=record h u
    let src:=hosts (point e).2
    ∃p back q,Gather.select (Gather.reaching near) (receiver e side) p=some (hosts h.1.2) ∧
      rawWord e side=Packed.token (some back) ∧ walk near src (path back) 4=some (receiver e side) ∧
      Gather.select (Gather.reaching near) (receiver e side) q=some src ∧
      value (Gather.reaching near) (receiver e side) p
        (shortPath (if r.target then r.neighbor.castSucc else Fin.last A.degree))=q.val+1 ∧
      Rebase.value near .path src back=q.val :=by
  intro h r src
  let t : Fin (2*A.cap):=⟨0,by have positive:=A.capPos;omega⟩
  have geom:=prior_head A native S ready (cableNames k rank) win (rotor A rank) he rank coord named fit winner
    (rotor_sorted A rank) (rotor_routes A native S ready rank) df order profile same lay a t
  obtain ⟨p,sp,_⟩:=ActorPath.received_once (rotor A rank) (fun z : J×V=>hosts z.2) near
    (fun z j v hit=>by rw [roster_mapped A groups hosts,hit];rfl) (reciprocal A hosts) _ _ _ geom
  have selected : Gather.select (Gather.reaching near) (receiver e side) p=some (hosts h.1.2) :=by
    exact (congrArg (fun v => Gather.select (Gather.reaching near) v p) atOwner).trans sp
  have reach:=selected
  unfold Gather.select at reach
  split at reach
  · contradiction
  · obtain ⟨back,q,word,forward,located,signed,reverse⟩:=original_previous_and_raw A native S ready groups hosts win he hm
      profile dest m hub lay bytes slots coord named fit winner df order same e side h u sameEdge p reach
    exact ⟨p,back,q,selected,word,forward,located,signed,reverse⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
