import OAI.Hierarchy.DescentDatedReturnedCableJobs
import OAI.Hierarchy.DescentPackedOperandPublic
import OAI.Hierarchy.DescentDatedOriginalOldSocket
import OAI.Hierarchy.DescentDatedOriginalPreferredHeaders

namespace OAI
/-! # The genuine old cable operand at an elected signed-material row -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentDatedAddressBook DescentParallelBase.ParentFilter
open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option cleanup.letToHave false
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000
variable {F P : Type} [Field F] (v:PhysicalOrdinary F P)
local notation "phys" => v.withIssuedSigned
local notation "S" => v.schedule
local notation "G" => v.gadget
local notation "A" => v.prior.placement
local notation "T" => (A).stage
local notation "D" => (A).degree
local notation "r" => 2^v.k
local notation "J" => (S).groupCount v.age
local notation "M" => (phys).material.oldLanes
local notation "H" => v.area.H
local notation "ss" => (phys).signed
local notation "native" => v.prior.order.trans Fin.valEmbedding
local notation "rank" => groupRank Fin.valEmbedding (v.prior.vertex.trans Fin.valEmbedding)
local notation "grp" => Equiv.refl (Fin J)
local notation "peers" => rotor A rank
local notation "home" => scanHomeAt v.nonnegative T
local notation "color" => scanColorAt v.nonnegative T
local notation "addr" => nativeAddress v.nonnegative T
local notation "rr" => BitDescription.scannedRows v.nonnegative T
local notation "K" => 2^(v.k+1)
local notation "s" => shape r D (2*(A).cap) v.profile
local notation "traffic" => nativeTraffic v.world.graph v.world.core home
local notation "fmt" => v.ticket.depotShape v.short
variable (oldFit : Fintype.card v.prior.V ≤ v.area.H)
    (R : Fin v.area.H → Fin v.prior.placement.degree → Option (Fin v.area.H))
local notation "hosts" => v.prior.vertex.trans (Fin.castLEEmb oldFit)
variable (selected : (v.prior.placement.stage.result v.nonnegative).Choice)
local notation "lay" => bestLayout (branchWidth G (fun _:(rr).pairs=>(T).z) ((rr).profile selected))
variable {w:ℕ} (m:Memory w) (parts:Bank)

variable (B:v.SelectedBoard oldFit R selected m parts)

open DescentDatedOperandCoordinates DescentDatedOperandReadPipeline DescentOperandPriorIncidence
open DescentHaloPackedRebase DescentSharedCableNames
local notation "ℒ" => (phys).resolver
local notation "E" => (phys).material
local notation "Γ" => (phys).ticketReadGeometry
local notation "pos_" => DescentSharedCableNames.Stage.Positive A
local notation "from_" q:arg => v.world.graph.src (q).val
local notation "block_" q:arg => (A).block (from_ q)
local notation "old_" => DescentSharedCableNames.Stage.outgoing A native S v.prior.valid
local notation "scene" => B.material
variable (bl : v.withIssuedSigned.resolver.blocks=v.withIssuedSigned.material.blocks) (hb : v.withIssuedSigned.resolver.hosts≤v.withIssuedSigned.material.hosts) (gs : v.withIssuedSigned.resolver.groups=v.withIssuedSigned.material.groups)
    (bands : (v.schedule.groupCount v.age)=v.withIssuedSigned.material.groups*v.withIssuedSigned.material.blocks)
local notation "seats" => breadth D*DepotRAM.Material.roles fmt
local notation "col" => (Fin (E).hosts→Fin (E).groups→Cell (E).fieldBits)
variable (serial peer : Fin v.withIssuedSigned.material.blocks→Fin (breadth v.prior.placement.degree*DepotRAM.Material.roles (v.ticket.depotShape v.short))→(Fin v.withIssuedSigned.material.hosts → Fin v.withIssuedSigned.material.groups → Cell v.withIssuedSigned.material.fieldBits))
variable (orig : Fin v.withIssuedSigned.resolver.jobs→Fin 6→Values v.withIssuedSigned.ticketReadGeometry v.withIssuedSigned.operandShortBits)
    (prior : Fin v.withIssuedSigned.resolver.jobs→Fin 4→Values v.withIssuedSigned.ticketReadGeometry (v.withIssuedSigned.resolver.size+2)) (born : Fin v.withIssuedSigned.resolver.jobs→Fin 3→Values v.withIssuedSigned.ticketReadGeometry v.withIssuedSigned.bornBook.bits)
local notation "data" => (phys).originalValues ((phys).sampleHeads bl hb gs orig prior born
  ((phys).wideMaterialValues R scene bands serial peer) ((phys).narrowValue R))
variable (j : Fin v.withIssuedSigned.resolver.jobs) (h : Fin v.withIssuedSigned.resolver.hosts) (y : Fin v.withIssuedSigned.resolver.groups) (recv : Fin v.area.H)
local notation "grpAt" => (finProdFinEquiv (y.cast gs,(phys).receiverBlock bl j)).cast bands.symm
variable (atHost : DepotRAM.Material.Route.receiver v.area.H v.withIssuedSigned.materialPitch (h.castLE hb)=some recv)
local notation "modeKey" p:arg x:arg old:arg mode:arg => finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,mode)))

local notation "live_" => DescentRawCablePanel.Live A (rr).pick
local notation "qAt" raw:arg => (⟨DescentCableDonorNames.anchor (rr).pick (raw).val,(raw).property⟩ : pos_)
local notation "whereAt" raw:arg => hosts ((A).pos (from_ (qAt raw))).2
local notation "seedAt" raw:arg => ((A).pos (from_ (qAt raw))).1
local notation "seatAt" raw:arg => ((block_ (qAt raw),old_ (qAt raw),DescentCableDonorNames.role (raw).val):DepotRAM.Material.Seat fmt)

open DescentDatedSourcePathDirectory DescentOrdinaryOriginPorts DescentOrdinaryOriginMask
local notation "walk_" => (phys).walkValues (Gather.reaching R)
local notation "fixed_" => SortedInput.values Γ data walk_
local notation "rank_" => (rankV Γ fixed_ j 0 h y).val
local notation "oldBlock_" => ((fixed_).origin j 2 h y).val
local notation "donor_" raw:arg => (fun _ : Fin (Γ).paths=>scene (whereAt raw) (seedAt raw))
local notation "reverse_" raw:arg => (fun _ : Fin (Γ).paths=>digest (DepotRAM.Material.reverseEntries fmt R (whereAt raw)))
local notation "row_" p:arg raw:arg => finProdFinEquiv (p,Ticket.seatNo (seatAt raw))
local notation "actual_" p:arg birthJob:arg raw:arg => Ticket.current (phys).materialFormat (donor_ raw) (reverse_ raw)
  birthJob (seatAt raw) (rawKey Γ fixed_ j h y) rank_ oldBlock_
  (((fixed_).raw j 6 (row_ p raw) h y).val) (((fixed_).raw j 7 (row_ p raw) h y).val)

local notation "N" => v.world.graph
local notation "canon" => hostRotor hosts (DescentGroupPeerOrder.hostRoster A ((hosts).trans Fin.valEmbedding))
local notation "names" => cableNames v.k rank
local notation "inlet" a:arg edge:arg live:arg => DescentTerminalPortChart.first A a edge live
local notation "saved" a:arg e:arg live:arg => DescentSharedCableNames.Stage.live A native S v.prior.valid names
  (DescentSharedCableNames.Stage.home A a) (inlet a e live)
variable (sameColor : ∀e∈v.world.core,scanColorAt v.nonnegative v.prior.placement.stage (v.world.graph.src e)=scanColorAt v.nonnegative v.prior.placement.stage (v.world.graph.dst e))
local notation "owner" => StarKeys.nativeKey N v.world.core home color (A).cap addr sameColor lay
local notation "venue" => newSite N (rr).pick lay (coloredPack N v.world.core home color (A).cap)
local notation "siteAt" e:arg side:arg => (if side then owner (venue (GadgetNetwork.target N (rr).pick (e).val))
  else owner (venue (GadgetNetwork.source N (e).val)))
local notation "signedBoard" => Prepare.signed A native S v.prior.valid (grp).toEmbedding hosts

/-- The terminal bank and the public grain presentation choose the same physical
wing for an original graph incidence, including a self-loop. -/
theorem registered_first_endpoint (a : (N).Site) (edge : Incident N a) (positive : 0<(A).grainCount edge.val) :
    saved a edge positive=DescentPackedOperand.Public.endpoint A native S v.prior.valid names
      (decide ((N).src edge.val≠a)) ⟨edge.val,⟨0,positive⟩⟩ :=by
  rcases edge with ⟨e, inc⟩
  by_cases src : v.world.graph.src e = a
  · subst a
    simp [DescentTerminalPortChart.first, DescentPackedOperand.Public.endpoint, Exchange.sourcePort]
  · have dst := inc.resolve_left src
    subst a
    simp [DescentTerminalPortChart.first, DescentPackedOperand.Public.endpoint, Exchange.targetPort, src]

private theorem previous_digit_room : max 1 (max (A).cap D)<2^(E).fieldBits:=by
  let layout:=v.signedLayout
  have cells:=layout.field_room.1
  have root : D+1≤breadth D:=by
    change D+1≤(D+1)^4
    simpa only [pow_one] using (Nat.pow_le_pow_right (Nat.zero_lt_succ D) (by decide : 1≤4))
  have slots:=real_catalogue_room v
  have sub : (A).cap≤r*(A).cap*11:=(Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)).trans
    (Nat.le_mul_of_pos_right _ (by decide : 0<11))
  change layout.rawAlphabet≤2^(E).fieldBits at cells
  change max 1 (max (A).cap D)<2^(E).fieldBits
  change breadth D+1+layout.lowSites+breadth D*breadth D*layout.lowSites+layout.tickets+(layout.newCap+1)+2≤2^(E).fieldBits at cells
  omega

include atHost in
/-- The physical old and source paths are chosen from the same roster actually used
by the installed B.material table. The native prior header prefers the source wing
also for a loop, in agreement with the original tensor operand. -/
theorem returned_old_socket_material (roster : R=canon) (a : (N).Site) (edge : Incident N a)
    (live : 0<(A).grainCount edge.val) (raw : live_) (side : Bool)
    (port : Stage.CablePort A v.nonnegative (⟨edge.val,live⟩ : pos_)
      (if (N).src edge.val=a then 0 else 1) (qAt raw) (DescentCableDonorNames.role raw.val))
    (atOwner : recv=hosts (siteAt raw side).1.2) (cohort : grpAt=((A).pos a).1)
    (ordinal : Fin (breadth D)) (chunk : ℕ)
    (cause : (orig j 0 h y).val=1) (stamp : (orig j 1 h y).val=ordinal.val)
    (sorted : DescentSortedRoster.indexed (Gather.reaching R) recv ordinal=some (hosts ((A).pos a).2))
    (block : (orig j 2 h y).val=((A).block a).val)
    (header : let d:=saved a edge live
      ∀f,(prior j f h y).val=(DescentOperandStateBanks.Pointer.cable d.neighbor.val d.wire.val chunk).header f) :
    ∃p : Fin (breadth D),Gather.select (Gather.reaching R) recv p=some (whereAt raw) ∧
      (rawKey Γ fixed_ j h y).val=Ticket.socket p false (seatAt raw) ∧
      ticketAt Γ fixed_ j h y=actual_ p false raw :=by
  subst R
  let q : pos_:=⟨edge.val,live⟩
  let d:=saved a edge live
  let target:=decide ((N).src edge.val≠a)
  have origPort : Stage.CablePort A v.nonnegative q (if target then 1 else 0) (qAt raw)
      (DescentCableDonorNames.role raw.val):=by
    by_cases atSrc:(N).src edge.val=a <;> simpa [target,atSrc,q] using port
  have pos:=Stage.CablePort.same_position A v.nonnegative origPort
  have coords:=Stage.old_socket_coordinates A a edge
  have cluster : grpAt=seedAt raw:=cohort.trans (coords.1.trans (congrArg Prod.fst pos))
  have baseBlock : (orig j 2 h y).val=(block_ q).val:=block.trans (congrArg Fin.val coords.2)
  obtain ⟨root,⟨visited,_⟩,_⟩:=Sorted.raw_at (Gather.reaching canon) recv _ ordinal sorted
  have reach : Gather.reaching canon recv root=some (hosts ((A).pos a).2):=by
    unfold Gather.select at visited;split at visited
    · contradiction
    · exact visited
  obtain ⟨back,p,_,_,located,_,_⟩:=Stage.original_birth_root A native S v.prior.valid grp hosts B.win
    v.nonnegative B.live v.profile B.births B.issued (A).hub lay (donorNameBits v.stage.k v.stage.Δ)
    (phys).materialFormat.slots v.prior.valid.coordinates B.named B.small B.winning B.degree B.ordered sameColor raw side
  have donor : Gather.select (Gather.reaching canon) recv p=some (whereAt raw):=by rw [atOwner];exact located
  have recovered : DescentSharedCableNames.Stage.recover A (DescentSharedCableNames.Stage.home A a)
      (inlet a edge live)=⟨edge.val,⟨0,live⟩⟩:=by
    unfold DescentTerminalPortChart.first
    split <;> rfl
  have previous:=DescentDatedSourcePathDirectory.previous_source A native S v.prior.valid
    ((grp).toEmbedding.trans Fin.valEmbedding) hosts (DescentSharedCableNames.Stage.home A a) (inlet a edge live)
    recv root p reach (by rw [recovered];change Gather.select _ recv p=some (hosts ((A).pos (from_ q)).2);rw [pos];exact donor)
  obtain ⟨slot,polarity,one,two,three⟩:=Stage.preferred_material_headers (short:=v.short) A native S v.prior.valid grp hosts
    B.win B.live v.profile B.births B.issued (A).hub lay (donorNameBits v.stage.k v.stage.Δ) a v.prior.valid.coordinates edge live (E).fieldBits
  change d.sourceWire=old_ q at slot
  change d.target=target at polarity
  have routed : value (Gather.reaching canon) recv root
      (shortPath (if target then d.neighbor.castSucc else Fin.last D))=p.val+1:=by
    rw [←polarity];exact previous
  have wide:=previous_digit_room v
  have fitOld : 1+d.sourceWire.val<2^(E).fieldBits:=by have:=d.sourceWire.isLt;omega
  have fitPeer : 1+d.neighbor.val<2^(E).fieldBits:=by have:=d.neighbor.isLt;omega
  have fitSide : d.target.toNat < 2^(E).fieldBits := by
    have bit : d.target.toNat ≤ 1 := by cases d.target <;> decide
    exact bit.trans_lt ((Nat.le_max_left 1 _).trans_lt wide)
  refine ⟨p,donor,?_⟩
  apply returned_old_occurrence v oldFit canon selected m parts B bl hb gs bands serial peer orig prior born j h y recv
    atHost q raw target origPort (hosts ((A).pos a).2) ordinal root p d.neighbor d.neighbor d.wire chunk cause stamp
    sorted baseBlock header visited _ routed donor cluster
  dsimp only
  rw [cohort,←coords.2]
  refine ⟨?_,?_,fun _=>?_⟩
  · exact (congrArg Fin.val three).trans ((Fin.val_cast_of_lt fitOld).trans
      (by rw [slot,Nat.add_comm]))
  · exact (congrArg Fin.val two).trans ((Fin.val_cast_of_lt fitSide).trans (congrArg Bool.toNat polarity))
  · exact (congrArg Fin.val one).trans ((Fin.val_cast_of_lt fitPeer).trans (Nat.add_comm _ _))

include atHost in
/-- The physical old and source paths are chosen from the same roster actually used
by the installed B.material table. The native prior header prefers the source wing
also for a loop, in agreement with the original tensor operand. -/
theorem returned_old_socket (roster : R=canon) (a : (N).Site) (edge : Incident N a)
    (live : 0<(A).grainCount edge.val) (raw : live_) (side : Bool)
    (port : Stage.CablePort A v.nonnegative (⟨edge.val,live⟩ : pos_)
      (if (N).src edge.val=a then 0 else 1) (qAt raw) (DescentCableDonorNames.role raw.val))
    (atOwner : recv=hosts (siteAt raw side).1.2) (cohort : grpAt=((A).pos a).1)
    (cables : Block v.k→Fin (2*(A).cap)→Bank) (memory : Memory w)
    (_signed : ∀x n,DescentPackedColony.Reads (cables x n) (fun h g=>DescentSignedCableCodec.encode (signedBoard x n h g)) M memory)
    (_wireWidth : DescentSignedCableCodec.width D (A).cap*M≤w)
    (ordinal : Fin (breadth D)) (chunk : ℕ)
    (cause : (orig j 0 h y).val=1) (stamp : (orig j 1 h y).val=ordinal.val)
    (sorted : DescentSortedRoster.indexed (Gather.reaching R) recv ordinal=some (hosts ((A).pos a).2))
    (block : (orig j 2 h y).val=((A).block a).val)
    (header : let d:=saved a edge live
      ∀f,(prior j f h y).val=(DescentOperandStateBanks.Pointer.cable d.neighbor.val d.wire.val chunk).header f) :
    ∃p : Fin (breadth D),Gather.select (Gather.reaching R) recv p=some (whereAt raw) ∧
      (rawKey Γ fixed_ j h y).val=Ticket.socket p false (seatAt raw) ∧
      ticketAt Γ fixed_ j h y=actual_ p false raw :=by
  exact returned_old_socket_material v oldFit R selected m parts B bl hb gs bands serial peer orig prior born
    j h y recv atHost sameColor roster a edge live raw side port atOwner cohort ordinal chunk cause stamp sorted block header

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
