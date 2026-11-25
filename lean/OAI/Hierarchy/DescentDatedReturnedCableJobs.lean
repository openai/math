import OAI.Hierarchy.DescentDatedSampledCableCatalog
import OAI.Hierarchy.DescentDatedReturnedOldSocket
import OAI.Hierarchy.DescentDatedReturnedBirthSocket
import OAI.Hierarchy.DescentIssuedOperandKey

namespace OAI
/-! # Returned operands on the actual elected cable and sorted donor path -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentDatedAddressBook DescentParallelBase.ParentFilter
open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
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

theorem original_port_page (birthJob : Bool) (q : pos_) (raw : live_) (mode : Fin 3)
    (port : Stage.CablePort A v.nonnegative q mode (qAt raw)
      (if birthJob then 0 else DescentCableDonorNames.role raw.val))
    (cohort : grpAt=seedAt raw) (f : Fin 5) :
    let idx:=if lt_ : mode.val<2 then DescentDatedOperandPages.anchor fmt (block_ q) (old_ q) ⟨mode.val,lt_⟩ f
      else DescentDatedOperandPages.sibling fmt (block_ q) (old_ q) f
    (DescentDatedOperandPages.law fmt v.profile (E).fieldBits idx.val
      (DepotRAM.combine fmt (scene (whereAt raw) grpAt))).val=Ticket.anchor birthJob (seatAt raw) f :=by
  intro idx
  have same_:=Stage.CablePort.same_position A v.nonnegative port
  have terrainEq : (scene (whereAt raw) grpAt).terrain=
      (Stage.nativeParts A native S v.prior.valid rank B.win grp hosts B.live v.profile B.births B.issued
        (hostRotor hosts (DescentGroupPeerOrder.hostRoster A ((hosts).trans Fin.valEmbedding))) (A).hub lay
        (donorNameBits v.stage.k v.stage.Δ) (hosts ((A).pos (from_ q)).2) ((A).pos (from_ q)).1).terrain :=by
    rw [cohort,same_];rfl
  have issued:=Stage.CablePort.page_at A native S v.prior.valid grp hosts B.win v.nonnegative B.live v.profile
    B.births B.issued (A).hub lay (donorNameBits v.stage.k v.stage.Δ) v.prior.valid.coordinates B.named B.small
    B.winning B.degree B.ordered B.topo B.matched B.width B.topology (E).fieldBits port (scene (whereAt raw) grpAt)
    terrainEq f
  have bounded:=Ticket.anchor_small birthJob (seatAt raw) (real_catalogue_room v) f
  cases birthJob <;> exact (congrArg Fin.val issued).trans (Fin.val_cast_of_lt bounded)

include atHost in
/-- Match and material columns are read directly from the physically elected board.
The origin and socket facts are the five scalar conclusions of the returned old
or newborn socket, including dense-to-four-hop ordinal translation. -/
theorem returned_selected_occurrence (p : Fin (breadth D)) (birthJob : Bool)
    (q : pos_) (raw : live_) (mode : Fin 3)
    (port : Stage.CablePort A v.nonnegative q mode (qAt raw)
      (if birthJob then 0 else DescentCableDonorNames.role raw.val))
    (live : Gather.select (Gather.reaching R) recv p=some (whereAt raw))
    (cohort : grpAt=seedAt raw)
    (present : (rawKey Γ fixed_ j h y).val=Ticket.socket p birthJob (seatAt raw))
    (cause : ((fixed_).origin j 0 h y).val=if birthJob then 2 else 1)
    (kind : ((fixed_).prior j 0 h y).val=1)
    (mouth : birthJob=true→((fixed_).mouth j 1 h y).val=(DescentCableDonorNames.role raw.val).val)
    (chosen : (anchorChoice Γ fixed_ j h y).val=(modeKey p (block_ q) (old_ q) mode).val+1) :
    ticketAt Γ fixed_ j h y=actual_ p birthJob raw :=by
  have location:=Stage.CablePort.same_position A v.nonnegative port
  have source : Gather.select (Gather.reaching R) recv p=some (hosts ((A).pos (from_ q)).2) :=by
    rw [location];exact live
  have groupAt : grpAt=((A).pos (from_ q)).1:=by rw [location];exact cohort
  apply ticketAt_selected Γ fixed_ j h y rfl rfl p birthJob (seatAt raw) (phys).materialFormat
    (donor_ raw) (reverse_ raw) (modeKey p (block_ q) (old_ q) mode) chosen present cause kind mouth
  · intro f _
    have read:=returned_anchor_pages v oldFit R selected m parts B bl hb gs bands serial peer orig prior born
      j h y recv atHost p q (qAt raw) mode _ port source groupAt f
    change ((data).anchor j f (modeKey p (block_ q) (old_ q) mode) h y).val=_
    exact read.trans (by cases birthJob <;> rfl)
  · intro f _
    exact returned_raw_pages v oldFit R selected m parts B bl hb gs bands serial peer orig prior born
      j h y recv atHost p raw live cohort f

include atHost in
/-- An old registered cable, starting from its four pointer words, its sorted W
origin, and the physically retained signed census of the incident wire. -/
theorem returned_old_occurrence (q : pos_) (raw : live_) (target : Bool)
    (port : Stage.CablePort A v.nonnegative q (if target then 1 else 0) (qAt raw) (DescentCableDonorNames.role raw.val))
    (actor : Fin H) (ordinal root p : Fin (breadth D)) (priorPeer neighbor : Fin D) (first : Fin (A).cap)
    (chunk : ℕ) (cause : (orig j 0 h y).val=1) (stamp : (orig j 1 h y).val=ordinal.val)
    (sorted : DescentSortedRoster.indexed (Gather.reaching R) recv ordinal=some actor)
    (block : (orig j 2 h y).val=(block_ q).val)
    (header : ∀f,(prior j f h y).val=(DescentOperandStateBanks.Pointer.cable priorPeer.val first.val chunk).header f)
    (visited : Gather.select (Gather.reaching R) recv root=some actor)
    (signedRows :
      let page (f : Fin 4) :=
        DescentDatedOperandPages.law fmt v.profile (E).fieldBits
          (DescentDatedOperandPages.header fmt (block_ q) priorPeer first f).val
          (DepotRAM.combine fmt (scene actor grpAt))
      (page 3).val=(old_ q).val+1 ∧ (page 2).val=target.toNat ∧ (target=true→(page 1).val=neighbor.val+1))
    (path : DescentDatedSourcePathDirectory.value (Gather.reaching R) recv root
      (shortPath (if target then neighbor.castSucc else Fin.last D))=p.val+1)
    (donated : Gather.select (Gather.reaching R) recv p=some (whereAt raw)) (cohort : grpAt=seedAt raw) :
    (rawKey Γ fixed_ j h y).val=Ticket.socket p false (seatAt raw) ∧
      ticketAt Γ fixed_ j h y=actual_ p false raw :=by
  have head:=original_port_page v oldFit R selected m parts B bl gs bands j y false q raw _ port cohort 4
  have select_:=(phys).sampled_old_sorted_socket bl hb gs R scene bands serial peer orig prior born j h y recv atHost
    actor (whereAt raw) ordinal root p (block_ q) priorPeer neighbor first (old_ q) target chunk (seatAt raw)
    cause stamp sorted block header visited (scene actor grpAt) rfl signedRows path donated (by
      cases target <;> exact head)
  rcases select_ with ⟨key,oldCause,kind,chosen,_⟩
  refine ⟨key,?_⟩
  exact returned_selected_occurrence v oldFit R selected m parts B bl hb gs bands serial peer orig prior born
    j h y recv atHost p false q raw _ port donated cohort key oldCause kind (by intro impossible;cases impossible) chosen

include atHost in
/-- A new six-party cable uses its authenticated W candidate, actual decoded
birth header and typed role. The source and sibling matcher pages come from the
original paired winner and the inverse table is indexed by the returned host. -/
theorem returned_birth_occurrence (q : pos_) (raw : live_) (second : Bool)
    (port : Stage.CablePort A v.nonnegative q (if second then 2 else 0) (qAt raw) 0)
    (chart : Return) (ordinal : Fin (breadth chart.degree)) (x₁ : Fin (2^chart.depth))
    (seat : Fin chart.capacity) (party : Fin 6) (node : Fin chart.newNodes)
    (word : Cell (chart.ordinalBits*chart.newNodes))
    (stamp : ((encode chart.ordinalBits chart.newNodes).symm word node).val=(candidate chart ordinal x₁ (.inr (seat,party))).val+1)
    (origin : ∀f,orig j f h y=readLaw chart (Γ).digitBits node f word)
    (idx p : Fin (breadth D)) (ordinalId : ordinal.val=idx.val) (blockId : x₁.val=(block_ q).val)
    (seatId : seat.val=(old_ q).val) (widthRoom : max 2 (max ordinal.val (max x₁.val seat.val))<2^(Γ).digitBits)
    (sorted : DescentSortedRoster.indexed (Gather.reaching R) recv idx=some (whereAt raw))
    (donated : Gather.select (Gather.reaching R) recv p=some (whereAt raw)) (cohort : grpAt=seedAt raw)
    (basis : DescentOrdinaryBorn.Spec) (arg scale prof : ℕ) (mouth : DescentOrdinaryBorn.Mouth)
    (live : DescentOrdinaryBorn.mouth basis scale prof party arg=some mouth) (mouthRoom : 11≤2^(phys).bornBook.bits)
    (header : (prior j 0 h y).val=(DescentOrdinaryBorn.field basis ((ℒ).size+2) 0 arg scale prof party).val)
    (ports : ∀f,(born j f h y).val=(DescentOrdinaryBorn.RolePorts.value (phys).bornBook.bits (some mouth) f).val)
    (side : mouth.anchor.val=second.toNat) (role : mouth.rawRole=(DescentCableDonorNames.role raw.val).val) :
    (rawKey Γ fixed_ j h y).val=Ticket.socket p true (seatAt raw) ∧
      ticketAt Γ fixed_ j h y=actual_ p true raw :=by
  have head:=original_port_page v oldFit R selected m parts B bl gs bands j y true q raw _ port cohort 4
  have select_:=(phys).sampled_birth_socket bl hb gs R scene bands serial peer orig prior born j h y recv atHost
    chart ordinal x₁ seat party node word stamp origin idx p (block_ q) (old_ q) (whereAt raw)
    ordinalId blockId seatId widthRoom sorted donated basis arg scale prof mouth live
    (by simpa only [Nat.pow_zero] using Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) (Nat.zero_lt_succ ((ℒ).size+1)))
    mouthRoom header ports second side (seatAt raw) role (by cases second <;> exact head)
  rcases select_ with ⟨key,birthCause,kind,mouthRead,chosen,_⟩
  refine ⟨key,?_⟩
  exact returned_selected_occurrence v oldFit R selected m parts B bl hb gs bands serial peer orig prior born
    j h y recv atHost p true q raw _ port donated cohort key birthCause kind (fun _=>mouthRead) chosen

include atHost in
theorem returned_birth_socket (q : pos_) (raw : live_) (second : Bool)
    (port : Stage.CablePort A v.nonnegative q (if second then 2 else 0) (qAt raw) 0)
    (chart : Return) (ordinal : Fin (breadth chart.degree)) (x₁ : Fin (2^chart.depth))
    (seat : Fin chart.capacity) (party : Fin 6) (node : Fin chart.newNodes)
    (word : Cell (chart.ordinalBits*chart.newNodes))
    (stamp : ((encode chart.ordinalBits chart.newNodes).symm word node).val=(candidate chart ordinal x₁ (.inr (seat,party))).val+1)
    (origin : ∀f,orig j f h y=readLaw chart (Γ).digitBits node f word)
    (idx : Fin (breadth D)) (ordinalId : ordinal.val=idx.val) (blockId : x₁.val=(block_ q).val)
    (seatId : seat.val=(old_ q).val) (widthRoom : max 2 (max ordinal.val (max x₁.val seat.val))<2^(Γ).digitBits)
    (sorted : DescentSortedRoster.indexed (Gather.reaching R) recv idx=some (hosts ((A).pos (from_ q)).2))
    (cohort : grpAt=((A).pos (from_ q)).1)
    (basis : DescentOrdinaryBorn.Spec) (arg scale prof : ℕ) (mouth : DescentOrdinaryBorn.Mouth)
    (live : DescentOrdinaryBorn.mouth basis scale prof party arg=some mouth) (mouthRoom : 11≤2^(phys).bornBook.bits)
    (header : (prior j 0 h y).val=(DescentOrdinaryBorn.field basis ((ℒ).size+2) 0 arg scale prof party).val)
    (ports : ∀f,(born j f h y).val=(DescentOrdinaryBorn.RolePorts.value (phys).bornBook.bits (some mouth) f).val)
    (side : mouth.anchor.val=second.toNat) (role : mouth.rawRole=(DescentCableDonorNames.role raw.val).val) :
    ∃p:Fin (breadth D), Gather.select (Gather.reaching R) recv p=some (whereAt raw) ∧
      (rawKey Γ fixed_ j h y).val=Ticket.socket p true (seatAt raw) ∧
      ticketAt Γ fixed_ j h y=actual_ p true raw :=by
  have location:=Stage.CablePort.same_position A v.nonnegative port
  rw [location] at sorted cohort
  obtain ⟨p,⟨visits,_⟩,_⟩:=Sorted.raw_at (Gather.reaching R) recv (whereAt raw) idx sorted
  refine ⟨p,visits,?_⟩
  exact returned_birth_occurrence v oldFit R selected m parts B bl hb gs bands serial peer orig prior born
    j h y recv atHost q raw second port chart ordinal x₁ seat party node word stamp origin idx p
    ordinalId blockId seatId widthRoom sorted visits cohort basis arg scale prof mouth live mouthRoom header ports side role


end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
