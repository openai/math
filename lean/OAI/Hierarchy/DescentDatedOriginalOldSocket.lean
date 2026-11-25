import OAI.Hierarchy.DescentDatedTicketSignedHeader
import OAI.Hierarchy.DescentDatedPreviousRawPath
import OAI.Hierarchy.DescentDatedSortedPathSocket

namespace OAI
/-! # The retained signed socket at the very walk selected by the native W decoder -/
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

open DescentOperandPriorIncidence DescentTerminalSignedGrainWord DescentTerminalPointerDigits
open DescentColonies DescentKernelHistory
local notation "board" => Prepare.signed A native S ready groups.toEmbedding hosts
variable (cables : Block k→Fin (2*A.cap)→Bank) (mem : Memory w)
    (prior : ∀x j,DescentPackedColony.Reads (cables x j) (fun h g=>DescentSignedCableCodec.encode (Prepare.signed A native S ready groups.toEmbedding hosts x j h g)) M mem)
    (wide : DescentSignedCableCodec.width A.degree A.cap*M≤w)

/-- The old incidence and the original positive source have the same archive
group and block even when this operand was attached to the other endpoint. -/
theorem old_socket_coordinates (v : W.graph.Site) (wire : Incident N v) :
    (A.pos v).1=(A.pos (W.graph.src wire.val)).1 ∧ A.block v=A.block (W.graph.src wire.val) :=by
  rcases wire.property with hit|hit
  · rw [hit]
    exact ⟨rfl,rfl⟩
  · obtain ⟨_,_,edge⟩:=Finset.mem_map.mp (A.peers wire.val).1
    have grp := congrArg Prod.fst edge
    exact ⟨(congrArg (fun y => (A.pos y).1) hit.symm).trans grp.symm,
      (congrArg A.block hit.symm).trans (A.same wire.val).symm⟩

set_option maxHeartbeats 1200000 in
include coord named fit winner df order prior wide in
theorem old_socket_from_original (e : DescentRawCablePanel.Live A pick) (side : Bool) (v : W.graph.Site)
    (wire : Incident N v) (positive : 0<A.grainCount wire.val)
    (u : A.CellPorts (A.pos v).1 (A.pos v).2 (A.block v))
    (atPort : DescentSharedCableNames.Stage.recover A (DescentSharedCableNames.Stage.home A v) u=⟨wire.val,⟨0,positive⟩⟩)
    (peer : Fin A.degree) (serial : Fin A.cap)
    (header : peer.val*A.cap+serial.val=(DescentTerminalPointerDigits.token A native S ready (cableNames k rank) v
      ⟨wire,⟨0,positive⟩⟩).1)
    (sourceRack : hosts (A.pos (W.graph.src wire.val)).2=hosts (point e).2)
    (outBits : ℕ) (larger : max 1 (max A.cap A.degree)<2^outBits)
    (ix : Fin (breadth A.degree))
    (indexed : DescentSortedRoster.indexed (Gather.reaching near) (receiver e side) ix=some (hosts (A.pos v).2)) :
    let h:=DescentSharedCableNames.Stage.home A v
    let src:=hosts (point e).2
    let data:=scene (hosts (A.pos v).2) (groups (A.pos v).1)
    let page:=fun f : Fin 4=>DescentDatedOperandPages.law fmt profile outBits
      (DescentDatedOperandPages.header fmt (A.block v) peer serial f).val (DepotRAM.combine fmt data)
    ∃(used : A.CellPorts (A.pos v).1 (A.pos v).2 (A.block v)), ∃ p back q,
      let r:=record h used
      (grain h used)=⟨wire.val,⟨0,positive⟩⟩ ∧
      A.block v=A.block (W.graph.src wire.val) ∧ r.sourceWire=out ⟨wire.val,positive⟩ ∧
      DescentDatedSourcePathDirectory.Sorted.rawAtOrdinal (Gather.reaching near) (receiver e side) ix=p.val ∧
      Gather.select (Gather.reaching near) (receiver e side) p=some (hosts (A.pos v).2) ∧
      (page 3).val=r.sourceWire.val+1 ∧ (page 2).val=r.target.toNat ∧ (page 1).val=r.neighbor.val+1 ∧
      value (Gather.reaching near) (receiver e side) p
        (shortPath (if r.target then r.neighbor.castSucc else Fin.last A.degree))=q.val+1 ∧
      Gather.select (Gather.reaching near) (receiver e side) q=some src ∧
      rawWord e side=Packed.token (some back) ∧ walk near src (path back) 4=some (receiver e side) ∧
      Rebase.value near .path src back=q.val := by
  intro h src data page
  obtain ⟨used,shared,_,one,two,three⟩:=native_previous_headers A native S ready groups hosts win hm
    profile dest m hub lay bytes cables mem prior wide v coord u wire positive atPort peer serial header outBits
  obtain ⟨p,⟨selected,actual⟩,_⟩:=DescentDatedSourcePathDirectory.Sorted.raw_at
    (Gather.reaching near) (receiver e side) _ ix indexed
  obtain ⟨back,q,backward,forward,donor,canonical,_⟩:=original_birth_root A native S ready groups hosts win
    he hm profile dest m hub lay bytes slots coord named fit winner df order same e side
  have reaching : Gather.reaching near (receiver e side) p=some (hosts (A.pos v).2):=by
    unfold Gather.select at selected
    split at selected
    · contradiction
    · exact selected
  have landed : Gather.select (Gather.reaching near) (receiver e side) q=
      some (hosts (A.pos (W.graph.src (grain h used).1)).2):=by
    have sameSrc := congrArg (fun edge => hosts (A.pos (W.graph.src edge)).2) (congrArg Sigma.fst shared)
    exact donor.trans (congrArg some (sameSrc.trans sourceRack).symm)
  have read:=DescentDatedSourcePathDirectory.previous_source A native S ready
    (groups.toEmbedding.trans Fin.valEmbedding) hosts h used (receiver e side) p q reaching landed
  have id:=(old_socket_coordinates A v wire).2
  have serialId : (record h used).sourceWire=out ⟨wire.val,positive⟩:=by
    change out ⟨(grain h used).1,_⟩=_
    exact congrArg out (Subtype.ext (congrArg Sigma.fst shared))
  let r:=record h used
  have slot : 1+r.sourceWire.val<2^outBits := by
    rw [Nat.add_comm]
    exact (Nat.succ_le_of_lt r.sourceWire.isLt).trans_lt
      (((Nat.le_max_left A.cap A.degree).trans (Nat.le_max_right _ _)).trans_lt larger)
  have neigh : 1+r.neighbor.val<2^outBits := by
    rw [Nat.add_comm]
    exact (Nat.succ_le_of_lt r.neighbor.isLt).trans_lt
      (((Nat.le_max_right A.cap A.degree).trans (Nat.le_max_right _ _)).trans_lt larger)
  have flag : r.target.toNat<2^outBits := by
    have bound (t : Bool) : t.toNat ≤ 1 := by cases t <;> decide
    exact (bound _).trans_lt ((Nat.le_max_left _ _).trans_lt larger)
  refine ⟨used,p,back,q,shared,id,serialId,actual,selected,?_,?_,?_,read,donor,backward,forward,canonical⟩
  · exact (congrArg Fin.val three).trans ((Fin.val_cast_of_lt slot).trans (Nat.add_comm _ _))
  · exact (congrArg Fin.val two).trans (Fin.val_cast_of_lt flag)
  · exact (congrArg Fin.val one).trans ((Fin.val_cast_of_lt neigh).trans (Nat.add_comm _ _))

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
