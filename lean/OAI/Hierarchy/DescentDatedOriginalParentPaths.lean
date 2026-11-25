import OAI.Hierarchy.DescentDatedOriginalParentMass
import OAI.Hierarchy.DescentParentFilterSource

namespace OAI
/-! # Original packed donor routes on both ends of a genuine surviving cable -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {k i z D wire hist w short a : ℕ}
variable {W : MarkedWorld F d P bits} {prior : Reached W G q ε S k i z D wire hist}
set_option quotPrecheck false
attribute [local irreducible] Stage.nativeParts physicalRows DepotRAM.chip packDonor StarKeys.nativeKey
local notation "A" => prior.placement
local notation "J" => Fin (S.groupCount i)
local notation "V" => prior.V
local notation "native" => prior.order.trans Fin.valEmbedding
local notation "rank" => groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)
variable {he : 0≤ε} {choice : (prior.placement.stage.result he).Choice}
    {n : Normalize ((prior.placement.stage.result he).state choice)}
variable {z' D' : ℕ} {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink prior he prior.placement.stage choice n next) (port : MeterPort prior)
local notation "H" => port.hosts
local notation "T" => (A).stage
local notation "home" => scanHomeAt he T
local notation "color" => scanColorAt he T
local notation "addr" => nativeAddress he T
local notation "r" => 2^k
local notation "rr" => BitDescription.scannedRows he T
local notation "lay" => bestLayout (branchWidth G (fun _ : (rr).pairs=>(T).z) ((rr).profile choice))
local notation "bytes" => donorNameBits (T).k (T).Δ
local notation "slots" => 2^(packExponent 20 (T).Δ)+2
local notation "gain" => gainExponent 20 (T).Δ
local notation "peers" => rotor A rank
local notation "grp" => Equiv.refl J
local notation "hosts" => port.vertex
variable (win : Fin (S.groupCount i)×prior.V→Fin (2^k)→Cell a) (hm : 0<port.groupsPerWord)
variable (named : prior.placement.SiteNamed (groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)))
    (fit : ∀u,(win (prior.placement.pos u) (prior.placement.block u)).val<2^short)
    (winner : ∀u,(win (prior.placement.pos u) (prior.placement.block u)).val=
      1+2*heap (nativeAddress he prior.placement.stage (scanHomeAt he prior.placement.stage u)).2+
        (scanColorAt he prior.placement.stage u).toNat)
    (df : prior.placement.degree<2^short)
    (order : ∀e f,(prior.order e).val<(prior.order f).val ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
variable (profile : ℕ)
variable (b : ℕ) (m : Memory w)
    (sumSize : (shape (2^k) prior.placement.degree (2*prior.placement.cap) profile).outputBits*port.groupsPerWord≤w)
    (stored :
      let rankAt:=groupRank (Fin.valEmbedding : Fin (S.groupCount i) ↪ ℕ) (prior.vertex.trans Fin.valEmbedding)
      let shape₀:=shape (2^k) prior.placement.degree (2*prior.placement.cap) profile
      let world:=terrain (short:=short) prior.placement (prior.order.trans Fin.valEmbedding)
        S prior.valid (cableNames k rankAt) win (rotor prior.placement rankAt)
      let partsAt:=spread (Equiv.refl (Fin (S.groupCount i))).toEmbedding port.vertex world
      let inputs:=Gather.flat (Gather.descriptorInputs (K:=2^(k+1)) shape₀ prior.placement.cap partsAt)
      ∀j,m (b+j.val)=((DescentPacking.PackedMatch.topologyWords (M:=port.groupsPerWord) shape₀ inputs j).val:Computability.VPVNP.BurstRAM.Word w))
variable (dest : ℕ) (issued : Memory w)
    (roster : Fin port.hosts→Fin prior.placement.degree→Option (Fin port.hosts))
    (mounted : ∀(z : Fin (S.groupCount i)×prior.V) j,roster (port.vertex z.2) j=
      (rotor prior.placement (groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)) z j).map
        (fun h=>port.vertex h.2))
local notation "fmt" => Stage.shapeOf (short:=short) A bytes
local notation "measured" => Stage.nativeParts (short:=short) A native S prior.valid rank win grp hosts hm profile dest issued roster (A).hub lay bytes

open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator

local notation "sampleSlot" => DescentRawCablePanel.slot A S prior.valid native hosts grp (rr).pick
local notation "oldPorts" => S.groupCount i*r*(A).cap

variable (birth :
    let stage:=prior.placement.stage
    let actor:=scanHomeAt he stage
    let tint:=scanColorAt he stage
    let flow:=nativeTraffic W.graph W.core actor
    let limit:=prior.placement.cap
    let shape₀:=shape (2^k) prior.placement.degree (2*limit) profile
    let cellAt:=Stage.slot he prior.placement (Equiv.refl (Fin (S.groupCount i))).toEmbedding port.vertex hm
    ∀c : ScanColonies he stage,∀e : Matched flow limit (thinList actor tint c) (thickList actor tint c),
      ∃j : Fin shape₀.pairs,j.val=(pairNumber (DescentPacking.amount (live flow))
        (slabPacking flow limit (thinList actor tint c) (thickList actor tint c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=DescentPacking.PackedMatch.SixBirths.slot (cellAt c).2 j q
        DescentPacking.PackedMatch.SixBirths.atom stage.z (digit (shape₀.digit+1) ip.val (issued (dest+(cellAt c).1.val)).val) ip.val=
          some (stage.z,DescentTerminalEpochFlags.encode ((BitDescription.scannedRows he stage).profile choice ⟨c,e⟩),q.val))

open DescentGroupPeerOrder DescentSharedCableNames DescentHaloWalkRAM DescentPackedColony
local notation "N" => rawGraph he T choice
local notation "owner" => rawOwner he T choice n ((rr).state choice) (originalId _)
local notation "positiveRows" => DescentRawCablePanel.Live A (rr).pick
local notation "homeAt" => newSite W.graph (rr).pick lay (rr).pack
local notation:max "targetAt" e:arg side:arg => ticket.donorKey (homeAt (if side then (N).dst (e).val else (N).src (e).val))

include mounted in
private theorem actual_near (g : J) (v : V) (j : Fin (A).degree) :
    roster (hosts v) j=hostRotor hosts (hostRoster A ((hosts).trans Fin.valEmbedding)) (hosts v) j :=by
  rw [mounted (g,v) j,rotor_group]
  have live : ∃u,hosts u=hosts v:=⟨v,rfl⟩
  rw [hostRotor,dite_eq_left live,(hosts).injective live.choose_spec]
  have same : (hosts).trans Fin.valEmbedding = prior.vertex.trans Fin.valEmbedding := by
    ext x
    rfl
  rw [same]
  cases hostRoster A (prior.vertex.trans Fin.valEmbedding) v j <;> rfl

set_option maxHeartbeats 700000 in
include named fit winner df order mounted in
theorem original_parent_endpoints (e : positiveRows) (different : owner ((N).src e.val)≠owner ((N).dst e.val)) :
    let z:=groupSeat (sampleSlot e).2
    ∃p : Walk×Walk,∀side : Bool,
      let idx:=ActorPath.index (A).degree (if side then p.2 else p.1)
      DepotRAM.atSeat fmt profile G.b slots side (measured (sampleSlot e).1 z.1) z.2.1 z.2.2.1 z.2.2.2 =
        Packed.token (some idx) ∧
      Gather.reaching roster (sampleSlot e).1 idx=some (hosts (targetAt e side).1.2) :=by
  intro z
  let anch:DescentSharedCableNames.Stage.Positive A:=⟨anchor (rr).pick e.val,e.property⟩
  let org:=(A).pos (W.graph.src anch.val)
  let orig:=DescentPacking.PackedMatch.Local.Stage.parentRows (short:=short) A native S prior.valid rank win profile lay anch (role e.val)
  have seen:=DescentPacking.PackedMatch.Local.Stage.parent_actual (short:=short) A native S prior.valid rank win he prior.valid.coordinates named fit
    winner df order profile ticket.donorChart.same lay e
  have chart : ticket.donorChart.col=addr:=eq_of_heq ticket.donorChart.native
  have key:ticket.donorKey=StarKeys.nativeKey W.graph W.core home color (T).cap addr ticket.donorChart.same lay :=by
    unfold OrdinaryLink.donorKey IssuedDonorChart.key
    exact congrArg (fun loc => StarKeys.nativeKey W.graph W.core home color (T).cap loc ticket.donorChart.same lay) chart
  have live : orig≠none :=by
    intro empty
    have same:=seen.1 empty
    have raw : n.destination (rawInput he T choice ((rr).state choice) ((N).src e.val)) =
        n.destination (rawInput he T choice ((rr).state choice) ((N).dst e.val)) :=
      ((IssuedRows.common_chart he T choice ticket.issued ((rr).state choice)).choose_spec.1.2 _ _).2
        (congrArg (fun x=>mergeHub ticket.donorHub (T).k gain (ticket.donorKey x)) same)
    exact different (congrArg (originalId _) raw)
  obtain ⟨p,got⟩:=Option.ne_none_iff_exists'.mp live
  have routed:=seen.2 p got
  have rotorOK (u : J×V) (j : Fin (A).degree) (v : J×V) (edge:peers u j=some v) :
      roster (hosts u.2) j=some (hosts v.2):=by rw [mounted u j,edge]; rfl
  refine ⟨p,fun side=>?_⟩
  have read:=DescentPacking.PackedMatch.Local.Stage.retained_path_mounted (short:=short) A native S prior.valid grp hosts win he hm profile dest
    issued (A).hub lay bytes slots prior.valid.coordinates named fit winner df order roster
    (actual_near port roster mounted org.1) anch (role e.val) side
  have look : DepotRAM.atSeat fmt profile G.b slots side (measured (sampleSlot e).1 z.1)
      z.2.1 z.2.2.1 z.2.2.2=Packed.token (some (ActorPath.index (A).degree (if side then p.2 else p.1))) :=by
    let x := (A).block (W.graph.src anch.val)
    let out := DescentSharedCableNames.Stage.outgoing A native S prior.valid anch
    have coords : z=(org.1,x,out,role e.val) := by
      change groupSeat (finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (org.1,x),out),role e.val))=_
      simp only [groupSeat, Equiv.symm_apply_apply]
    have sameV : (hosts).trans Fin.valEmbedding = prior.vertex.trans Fin.valEmbedding := by ext v; rfl
    have sameJ : (grp).toEmbedding.trans Fin.valEmbedding = (Fin.valEmbedding : J ↪ ℕ) := by ext v; rfl
    have rankEq : groupRank ((grp).toEmbedding.trans Fin.valEmbedding) ((hosts).trans Fin.valEmbedding)=rank :=
      congrArg₂ groupRank sameJ sameV
    let claim (ords : J × V ↪ ℕ) := DepotRAM.atSeat fmt profile G.b slots side
      (Stage.nativeParts (short:=short) A native S prior.valid ords win grp hosts hm profile dest issued
        roster (A).hub lay bytes (hosts org.2) org.1) x out (role e.val) =
      ParentIncidence.pathCell (A).degree side (DescentPacking.PackedMatch.Local.Stage.parentRows
        (short:=short) A native S prior.valid ords win profile lay anch (role e.val))
    have mountedRead : claim rank := Eq.mp (congrArg claim rankEq) read
    simp only [coords]
    exact mountedRead.trans (congrArg (ParentIncidence.pathCell (A).degree side) got)
  refine ⟨look,?_⟩
  rw [key]
  cases side
  · exact ActorPath.emitted peers (fun z=>hosts z.2) roster rotorOK org p.1 _ routed.src
  · exact ActorPath.emitted peers (fun z=>hosts z.2) roster rotorOK org p.2 _ routed.dst

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
