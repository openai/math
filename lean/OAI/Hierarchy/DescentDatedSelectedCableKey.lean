import OAI.Hierarchy.DescentDatedDecodedJobKey
import OAI.Hierarchy.DescentDatedReturnedCableJobs
import OAI.Hierarchy.DescentDatedReturnedCableKey

namespace OAI
/-! # Original semantic cable keys on the selected physical chronology -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentDatedAddressBook DescentParallelBase.ParentFilter
open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] (v:PhysicalOrdinary F P)
variable (selected : (v.prior.placement.stage.result v.nonnegative).Choice)

/-- Transport to the exact selected old placement. Both the split/normalization
and its ordinary receipt are the ones carried by the physical chronology. -/
structure AtSelected where
  norm : Hierarchy.DescentSixParty.Normalize ((v.prior.placement.stage.result v.nonnegative).state selected)
  next : Reached norm.result v.gadget v.q v.ε v.schedule v.k (v.age+1) v.nextZ v.nextDegree v.wire v.hist
  link : OrdinaryLink v.prior v.nonnegative v.prior.placement.stage selected norm next
  originalNorm : HEq norm v.normalize
  originalNext : HEq next v.target
  originalLink : HEq link v.ticket

def atSelected (choiceEq:HEq selected v.choice) : AtSelected v selected :=by
  cases v with
  | mk d bits G S q u eps k date z degree wire hist nz nd W prior he T c n target link old reference bornBook
      ingress raster vector resolver origin palette repack metadata operandBook signed venue level b short payload unit profile seats =>
    obtain rfl:=link.sourceRate
    obtain rfl:=eq_of_heq link.placement
    have selectedEq : selected = c := eq_of_heq choiceEq
    subst selected
    exact ⟨n,target,link,HEq.rfl,HEq.rfl,HEq.rfl⟩


end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

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
set_option maxHeartbeats 720000
variable {F P : Type} [Field F] (v:PhysicalOrdinary F P)
local notation "phys" => v.withIssuedSigned
local notation "S" => v.schedule
local notation "G" => v.gadget
local notation "A" => v.prior.placement
local notation "T" => (A).stage
local notation "D" => (A).degree
local notation "H" => v.area.H
local notation "native" => v.prior.order.trans Fin.valEmbedding
local notation "home" => scanHomeAt v.nonnegative T
local notation "color" => scanColorAt v.nonnegative T
local notation "addr" => nativeAddress v.nonnegative T
local notation "rr" => BitDescription.scannedRows v.nonnegative T
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
local notation "E" => (phys).material
local notation "pos_" => DescentSharedCableNames.Stage.Positive A
local notation "from_" q:arg => v.world.graph.src (q).val
local notation "block_" q:arg => (A).block (from_ q)
local notation "old_" => DescentSharedCableNames.Stage.outgoing A native S v.prior.valid
local notation "scene" => B.material
local notation "live_" => DescentRawCablePanel.Live A (rr).pick
local notation "qAt" raw:arg => (⟨DescentCableDonorNames.anchor (rr).pick (raw).val,(raw).property⟩ : pos_)
local notation "whereAt" raw:arg => hosts ((A).pos (from_ (qAt raw))).2
local notation "seedAt" raw:arg => ((A).pos (from_ (qAt raw))).1
local notation "seatAt" raw:arg => ((block_ (qAt raw),old_ (qAt raw),DescentCableDonorNames.role (raw).val):DepotRAM.Material.Seat fmt)


open DescentPackedOperand DescentOperandStateBanks DescentDatedPriorOperand
variable (choiceEq:HEq selected v.choice)
local notation "ac" => atSelected v selected choiceEq
local notation "net_" => (rawGraph v.nonnegative T selected)
local notation "oldSite_" => ((originalId (((T).result v.nonnegative).state selected).graph.Site) ∘ rawInput v.nonnegative T selected ((rr).state selected))
local notation "owner_" => rawOwner v.nonnegative T selected (ac).norm ((rr).state selected) (originalId _)
local notation "canon_" => hostRotor hosts (DescentGroupPeerOrder.hostRoster A ((hosts).trans Fin.valEmbedding))
local notation "own_" => StarKeys.nativeKey v.world.graph v.world.core home color (T).cap addr (ac).link.donorChart.same lay
local notation "pack_" => coloredPack v.world.graph v.world.core home color (A).cap
local notation "zone_" raw:arg => newSite v.world.graph (rr).pick lay pack_ (GadgetNetwork.source v.world.graph (raw).val)
/-- The observable digits for one selected board, with the reported ticket and its finite word kept as parameters. -/
private def selectedDigitsOnBoard : Prop := ∀ (l : DescentDatedPriorOperand.Layout)
    (_job : Fin l.jobs) (_host : Fin l.hosts) (_group : Fin l.groups)
    {paths socketBits : ℕ} (p : Fin paths) (birthJob : Bool) (raw : live_)
    (socket_ : Cell socketBits) (priorRank xOld serial_ peer_ : ℕ) (out : Fin 8 → ℕ)
    (_route : socket_.val = Ticket.socket p birthJob (seatAt raw))
    (_earned : out = Ticket.current (phys).materialFormat
      (fun _ : Fin paths => scene (whereAt raw) (seedAt raw))
      (fun _ : Fin paths => DescentHaloPackedRebase.digest (DepotRAM.Material.reverseEntries fmt R (whereAt raw)))
      birthJob (seatAt raw) socket_ priorRank xOld serial_ peer_)
    (listed:∀u t,t∈(A).near u→∃i,R (hosts u) i=some (hosts t))
    (_agrees:∀u i,R (hosts u) i=canon_ (hosts u) i)
    (_symmetric:∀u t i,R u i=some t→∃z,R t z=some u),
    let first:=decide (oldSite_ ((net_).src (raw).val)=oldSite_ ((net_).dst (raw).val))
    let second:=!first && decide (owner_ ((net_).src (raw).val)=owner_ ((net_).dst (raw).val))
    let marked:=DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role (raw).val) (decide ((qAt raw).val∈v.world.core))
    let halo:=DescentHaloCompilation.atSource (A).near hosts R listed (A).pos (A).block v.prior.valid.coordinates own_
    ∃hid : from_ (qAt raw)∈halo.member (zone_ raw),
      let donor:=(halo.slot (zone_ raw) ⟨from_ (qAt raw),hid⟩).val
      out=postedVector donor first second marked serial_ peer_ (old_ (qAt raw)).val
        (DescentCableDonorNames.role (raw).val).val
private theorem physicalDonorRoom : 0<(E).fieldBits ∧ breadth D<2^(E).fieldBits := by
  have range : breadth D<2^(E).fieldBits:=by
    have a:=v.signedLayout.field_room.1
    change v.signedLayout.rawAlphabet≤2^v.signedLayout.fieldBits at a
    have order : breadth D<v.signedLayout.rawAlphabet:=by
      unfold SignedStage.rawAlphabet
      change breadth D < breadth D+1+_+_+_+_+2
      omega
    exact order.trans_le a
  have positive : 0<(E).fieldBits:=by
    by_contra! zero
    have eqzero:(E).fieldBits=0:=Nat.eq_zero_of_le_zero zero
    rw [eqzero,pow_zero] at range
    exact (Nat.not_lt_of_ge (show 1≤breadth D from Nat.pos_of_ne_zero (pow_ne_zero 4 (Nat.succ_ne_zero D)))) range
  exact ⟨positive,range⟩
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
noncomputable section
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentDatedAddressBook DescentParallelBase.ParentFilter
open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
open DescentPackedOperand DescentOperandStateBanks DescentDatedPriorOperand
variable {F P : Type} [Field F]
private def digitsAtChoice (v : PhysicalOrdinary F P) (oldFit : Fintype.card v.prior.V ≤ v.area.H)
    (R : Fin v.area.H → Fin v.prior.placement.degree → Option (Fin v.area.H))
    (sel : (v.prior.placement.stage.result v.nonnegative).Choice) (eq : HEq sel v.choice) : Prop :=
  ∀ {w : ℕ} (m : Memory w) (parts : Bank) (B : v.SelectedBoard oldFit R sel m parts),
    selectedDigitsOnBoard v oldFit R sel m parts B eq

/-- Keep the board predicate folded while the chronological record is transported to its actual source rate and placement. -/
private def physicalDigitStatement (v : PhysicalOrdinary F P) : Prop :=
  ∀ (oldFit : Fintype.card v.prior.V ≤ v.area.H)
    (R : Fin v.area.H → Fin v.prior.placement.degree → Option (Fin v.area.H))
    (sel : (v.prior.placement.stage.result v.nonnegative).Choice) (eq : HEq sel v.choice),
    digitsAtChoice v oldFit R sel eq
attribute [local irreducible] physicalDigitStatement digitsAtChoice selectedDigitsOnBoard
set_option maxRecDepth 12000
set_option maxHeartbeats 350000
private theorem installedBoardDigits (v : PhysicalOrdinary F P) : physicalDigitStatement v := by

  obtain ⟨positive,range⟩ := physicalDonorRoom v

  cases v with
  | mk d bits gadget₀ sched₀ q u eps k date z degree wire hist nz nd W prior₀ he stage₀ c n target link prev reference bornBook
      ingress raster vector resolver origin palette repack metadata operandBook signed venue level b short payload unit profile seatCount =>

    obtain rfl:=link.sourceRate

    obtain rfl:=eq_of_heq link.placement

    unfold physicalDigitStatement
    intro oldFit R selected choiceEq
    have selectedEq : selected = c := eq_of_heq choiceEq
    subst selected

    unfold digitsAtChoice
    intro w m parts B

    unfold selectedDigitsOnBoard
    intro l j h y paths socketBits p birthJob raw socket_ priorRank xOld serial_ peer_ out route earned listed agrees symmetric
    let port:MeterPort prior₀:=⟨2^level,oldFit,0,0,DescentSIMDLookup.lanes payload (link.installedDonorWidth short profile)⟩

    exact OrdinaryLink.returned_cable_digits (short:=short) (prior:=prior₀) (choice:=c) (next:=target) link port B.win B.live B.named B.small B.winning B.degree B.ordered
      profile B.topo B.matched B.width B.topology B.births B.issued R B.neighbors B.offspring _ _
      l (fun _ _ _ => out) p birthJob raw socket_ route positive range.le listed agrees symmetric j h y priorRank xOld serial_ peer_ earned


end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

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
set_option maxHeartbeats 720000
variable {F P : Type} [Field F] (v:PhysicalOrdinary F P)
local notation "phys" => v.withIssuedSigned
local notation "S" => v.schedule
local notation "G" => v.gadget
local notation "A" => v.prior.placement
local notation "T" => (A).stage
local notation "D" => (A).degree
local notation "r" => 2^v.k
local notation "H" => v.area.H
local notation "native" => v.prior.order.trans Fin.valEmbedding
local notation "home" => scanHomeAt v.nonnegative T
local notation "color" => scanColorAt v.nonnegative T
local notation "addr" => nativeAddress v.nonnegative T
local notation "rr" => BitDescription.scannedRows v.nonnegative T
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
local notation "Γ" => (phys).ticketReadGeometry
local notation "pos_" => DescentSharedCableNames.Stage.Positive A
local notation "from_" q:arg => v.world.graph.src (q).val
local notation "block_" q:arg => (A).block (from_ q)
local notation "old_" => DescentSharedCableNames.Stage.outgoing A native S v.prior.valid
local notation "scene" => B.material
variable (bl : v.withIssuedSigned.resolver.blocks=v.withIssuedSigned.material.blocks) (hb : v.withIssuedSigned.resolver.hosts≤v.withIssuedSigned.material.hosts) (gs : v.withIssuedSigned.resolver.groups=v.withIssuedSigned.material.groups)
    (bands : (v.schedule.groupCount v.age)=v.withIssuedSigned.material.groups*v.withIssuedSigned.material.blocks)
variable (serial peer : Fin v.withIssuedSigned.material.blocks→Fin (breadth v.prior.placement.degree*DepotRAM.Material.roles (v.ticket.depotShape v.short))→(Fin v.withIssuedSigned.material.hosts → Fin v.withIssuedSigned.material.groups → Cell v.withIssuedSigned.material.fieldBits))
variable (orig : Fin v.withIssuedSigned.resolver.jobs→Fin 6→Values v.withIssuedSigned.ticketReadGeometry v.withIssuedSigned.operandShortBits)
    (prior : Fin v.withIssuedSigned.resolver.jobs→Fin 4→Values v.withIssuedSigned.ticketReadGeometry (v.withIssuedSigned.resolver.size+2)) (born : Fin v.withIssuedSigned.resolver.jobs→Fin 3→Values v.withIssuedSigned.ticketReadGeometry v.withIssuedSigned.bornBook.bits)
local notation "data" => (phys).originalValues ((phys).sampleHeads bl hb gs orig prior born
  ((phys).wideMaterialValues R scene bands serial peer) ((phys).narrowValue R))
variable (j : Fin v.withIssuedSigned.resolver.jobs) (h : Fin v.withIssuedSigned.resolver.hosts) (y : Fin v.withIssuedSigned.resolver.groups)

local notation "live_" => DescentRawCablePanel.Live A (rr).pick
local notation "qAt" raw:arg => (⟨DescentCableDonorNames.anchor (rr).pick (raw).val,(raw).property⟩ : pos_)
local notation "whereAt" raw:arg => hosts ((A).pos (from_ (qAt raw))).2
local notation "seedAt" raw:arg => ((A).pos (from_ (qAt raw))).1
local notation "seatAt" raw:arg => ((block_ (qAt raw),old_ (qAt raw),DescentCableDonorNames.role (raw).val):DepotRAM.Material.Seat fmt)


open DescentDatedSourcePathDirectory DescentOrdinaryOriginPorts DescentOrdinaryOriginMask
local notation "walk_" => (phys).walkValues (Gather.reaching R)
private def selectedCableInput := SortedInput.values Γ data walk_
local notation "fixed_" => selectedCableInput
  (v := v) (oldFit := oldFit) (R := R) (selected := selected) (m := m) (parts := parts) (B := B)
  (bl := bl) (hb := hb) (gs := gs) (bands := bands) (serial := serial) (peer := peer)
  (orig := orig) (prior := prior) (born := born)
attribute [local irreducible] selectedCableInput
local notation "rank_" => (rankV Γ fixed_ j 0 h y).val
local notation "oldBlock_" => ((fixed_).origin j 2 h y).val
local notation "donor_" raw:arg => (fun _ : Fin (Γ).paths=>scene (whereAt raw) (seedAt raw))
local notation "reverse_" raw:arg => (fun _ : Fin (Γ).paths=>digest (DepotRAM.Material.reverseEntries fmt R (whereAt raw)))
local notation "row_" p:arg raw:arg => finProdFinEquiv (p,Ticket.seatNo (seatAt raw))
local notation "actual_" p:arg birthJob:arg raw:arg => Ticket.current (phys).materialFormat (donor_ raw) (reverse_ raw)
  birthJob (seatAt raw) (rawKey Γ fixed_ j h y) rank_ oldBlock_
  (((fixed_).raw j 6 (row_ p raw) h y).val) (((fixed_).raw j 7 (row_ p raw) h y).val)


open DescentPackedOperand DescentOperandStateBanks DescentDatedPriorOperand
variable (choiceEq:HEq selected v.choice)
local notation "ac" => atSelected v selected choiceEq
local notation "net_" => (rawGraph v.nonnegative T selected)
local notation "oldSite_" => ((originalId (((T).result v.nonnegative).state selected).graph.Site) ∘ rawInput v.nonnegative T selected ((rr).state selected))
local notation "owner_" => rawOwner v.nonnegative T selected (ac).norm ((rr).state selected) (originalId _)
local notation "canon_" => hostRotor hosts (DescentGroupPeerOrder.hostRoster A ((hosts).trans Fin.valEmbedding))
local notation "own_" => StarKeys.nativeKey v.world.graph v.world.core home color (T).cap addr (ac).link.donorChart.same lay
local notation "pack_" => coloredPack v.world.graph v.world.core home color (A).cap
local notation "zone_" raw:arg => newSite v.world.graph (rr).pick lay pack_ (GadgetNetwork.source v.world.graph (raw).val)
private def selectedCableWord := ticketAt Γ fixed_
local notation "word_" => selectedCableWord
  (v := v) (oldFit := oldFit) (R := R) (selected := selected) (m := m) (parts := parts) (B := B)
  (bl := bl) (hb := hb) (gs := gs) (bands := bands) (serial := serial) (peer := peer)
  (orig := orig) (prior := prior) (born := born)
variable (old:Books v.withIssuedSigned.resolver) (typed:BookPointers old) (grain:Cell (v.withIssuedSigned.resolver.size+2))
local notation "side_" => fun j h y=>DescentDatedPublicGrain.withGrain grain (Ticket.recordedSide (ℒ).size (word_ j h y))
local notation "role_" => fun j f h y=>Ticket.recordedRole (ℒ).size (word_ j h y) f
variable (nameRoom :
    let digits := selectedCableWord
      (v := v) (oldFit := oldFit) (R := R) (selected := selected) (m := m) (parts := parts) (B := B)
      (bl := bl) (hb := hb) (gs := gs) (bands := bands) (serial := serial) (peer := peer)
      (orig := orig) (prior := prior) (born := born)
    ∀ j h y, 11 * (Ticket.recordedRole v.withIssuedSigned.resolver.size (digits j h y) 1).val +
      (Ticket.recordedRole v.withIssuedSigned.resolver.size (digits j h y) 2).val < 2^(v.withIssuedSigned.resolver.size+2))
local notation "jobs_" => ofBooks old typed side_ role_ nameRoom

/-- The true fixed resolver job at this chronology, observed from the selected
board, with both captures in the genuine donor chart and a signed public
fragment on the surviving branch. The socket pair is produced by either
`returned_old_occurrence` or `returned_birth_occurrence` in this same namespace. -/
theorem returned_cable_digits (p:Fin (breadth D)) (birthJob:Bool) (raw:live_)
    (observed : (rawKey Γ fixed_ j h y).val=Ticket.socket p birthJob (seatAt raw) ∧
      ticketAt Γ fixed_ j h y=actual_ p birthJob raw)
    (listed:∀u t,t∈(A).near u→∃i,R (hosts u) i=some (hosts t))
    (agrees:∀u i,R (hosts u) i=canon_ (hosts u) i)
    (symmetric:∀u t i,R u i=some t→∃z,R t z=some u) :
    let first:=decide (oldSite_ ((net_).src (raw).val)=oldSite_ ((net_).dst (raw).val))
    let second:=!first && decide (owner_ ((net_).src (raw).val)=owner_ ((net_).dst (raw).val))
    let marked:=DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role (raw).val) (decide ((qAt raw).val∈v.world.core))
    let halo:=DescentHaloCompilation.atSource (A).near hosts R listed (A).pos (A).block v.prior.valid.coordinates own_
    let dest:=((fixed_).raw j 7 (row_ p raw) h y).val
    let start:=((fixed_).raw j 6 (row_ p raw) h y).val
    ∃hid : from_ (qAt raw)∈halo.member (zone_ raw),
      let donor:=(halo.slot (zone_ raw) ⟨from_ (qAt raw),hid⟩).val
      word_ j h y=postedVector donor first second marked start dest (old_ (qAt raw)).val
        (DescentCableDonorNames.role (raw).val).val :=by
  exact installedBoardDigits v oldFit R selected choiceEq m parts B ℒ j h y p birthJob raw
    (rawKey Γ fixed_ j h y) rank_ oldBlock_
    (((fixed_).raw j 6 (row_ p raw) h y).val) (((fixed_).raw j 7 (row_ p raw) h y).val)
    (word_ j h y) observed.1 observed.2 listed agrees symmetric
set_option maxHeartbeats 1400000 in
theorem returned_cable_key (p:Fin (breadth D)) (birthJob:Bool) (raw:live_)
    (observed : (rawKey Γ fixed_ j h y).val=Ticket.socket p birthJob (seatAt raw) ∧
      ticketAt Γ fixed_ j h y=actual_ p birthJob raw)
    (listed:∀u t,t∈(A).near u→∃i,R (hosts u) i=some (hosts t))
    (agrees:∀u i,R (hosts u) i=canon_ (hosts u) i)
    (symmetric:∀u t i,R u i=some t→∃z,R t z=some u)
    (prevPeer prevSerial piece:ℕ)
    (read:∀f,(booksHeader old j h y f).val=(Pointer.cable prevPeer prevSerial piece).header f)
    (donorFit : breadth D*r≤2^((ℒ).size+2)) (codeFit : 11*(A).cap≤2^((ℒ).size+2)) :
    let first:=decide (oldSite_ ((net_).src (raw).val)=oldSite_ ((net_).dst (raw).val))
    let second:=!first && decide (owner_ ((net_).src (raw).val)=owner_ ((net_).dst (raw).val))
    let marked:=DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role (raw).val) (decide ((qAt raw).val∈v.world.core))
    let halo:=DescentHaloCompilation.atSource (A).near hosts R listed (A).pos (A).block v.prior.valid.coordinates own_
    let dest:=((fixed_).raw j 7 (row_ p raw) h y).val
    let start:=((fixed_).raw j 6 (row_ p raw) h y).val
    let scalar:=11*(old_ (qAt raw)).val+(DescentCableDonorNames.role (raw).val).val
    let cap_:piece<2^((ℒ).size+2):=(read 3).ge.trans_lt (booksHeader old j h y 3).isLt
    ∃hid : from_ (qAt raw)∈halo.member (zone_ raw),
      let donor:=(halo.slot (zone_ raw) ⟨from_ (qAt raw),hid⟩).val
      resolve (((jobs_) j).compiled h y)=if first then Key.first donor 0 scalar piece
        else if second then Key.second donor 0 scalar piece
        else resolve (Public.fragment marked (dest:Cell ((ℒ).size+2)) (start:Cell ((ℒ).size+2)) ⟨piece,cap_⟩ grain) :=by
  intro first second marked halo dest start scalar cap_
  have earned := returned_cable_digits (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected)
    (m:=m) (parts:=parts) (B:=B) (bl:=bl) (hb:=hb) (gs:=gs) (bands:=bands)
    (serial:=serial) (peer:=peer) (orig:=orig) (prior:=prior) (born:=born)
    (j:=j) (h:=h) (y:=y) (choiceEq:=choiceEq) p birthJob raw observed listed agrees symmetric
  let hid := Exists.choose earned
  have report := Exists.choose_spec earned
  refine ⟨hid,?_⟩
  intro donor
  have nameFit : scalar<2^((ℒ).size+2):=by
    have bound:=(finProdFinEquiv (old_ (qAt raw),DescentCableDonorNames.role (raw).val)).isLt
    simp only [finProdFinEquiv_apply_val] at bound
    exact (by dsimp only [scalar];omega : scalar<(A).cap*11).trans_le ((Nat.mul_comm _ _).le.trans codeFit)
  exact returned_key ℒ old typed word_ grain nameRoom j h y prevPeer prevSerial piece read donor first second marked
    start dest _ _ (fun hit=>by simp [second,hit]) report ((halo.slot _ ⟨_,hid⟩).isLt.trans_le donorFit) nameFit

set_option maxHeartbeats 1400000 in
theorem returned_cable_key_decoded (p:Fin (breadth D)) (birthJob:Bool) (raw:live_)
    (observed : (rawKey Γ fixed_ j h y).val=Ticket.socket p birthJob (seatAt raw) ∧
      ticketAt Γ fixed_ j h y=actual_ p birthJob raw)
    (listed:∀u t,t∈(A).near u→∃i,R (hosts u) i=some (hosts t))
    (agrees:∀u i,R (hosts u) i=canon_ (hosts u) i)
    (symmetric:∀u t i,R u i=some t→∃z,R t z=some u)
    (prevPeer prevSerial piece:ℕ)
    (read:∀f,(booksHeader old j h y f).val=(Pointer.cable prevPeer prevSerial piece).header f)
    (donorFit : breadth D*r≤2^((ℒ).size+2)) (codeFit : 11*(A).cap≤2^((ℒ).size+2)) :
    let first:=decide (oldSite_ ((net_).src (raw).val)=oldSite_ ((net_).dst (raw).val))
    let second:=!first && decide (owner_ ((net_).src (raw).val)=owner_ ((net_).dst (raw).val))
    let marked:=DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role (raw).val) (decide ((qAt raw).val∈v.world.core))
    let halo:=DescentHaloCompilation.atSource (A).near hosts R listed (A).pos (A).block v.prior.valid.coordinates own_
    let dest:=((fixed_).raw j 7 (row_ p raw) h y).val
    let start:=((fixed_).raw j 6 (row_ p raw) h y).val
    let scalar:=11*(old_ (qAt raw)).val+(DescentCableDonorNames.role (raw).val).val
    let cap_:piece<2^((ℒ).size+2):=(read 3).ge.trans_lt (booksHeader old j h y 3).isLt
    ∃hid : from_ (qAt raw)∈halo.member (zone_ raw),
      let donor:=(halo.slot (zone_ raw) ⟨from_ (qAt raw),hid⟩).val
      resolve (((decodedBooks old side_ role_ nameRoom) j).compiled h y)=if first then Key.first donor 0 scalar piece
        else if second then Key.second donor 0 scalar piece
        else resolve (Public.fragment marked (dest:Cell ((ℒ).size+2)) (start:Cell ((ℒ).size+2)) ⟨piece,cap_⟩ grain) :=by
  intro first second marked halo dest start scalar cap_
  have earned := returned_cable_digits (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected)
    (m:=m) (parts:=parts) (B:=B) (bl:=bl) (hb:=hb) (gs:=gs) (bands:=bands)
    (serial:=serial) (peer:=peer) (orig:=orig) (prior:=prior) (born:=born)
    (j:=j) (h:=h) (y:=y) (choiceEq:=choiceEq) p birthJob raw observed listed agrees symmetric
  let hid := Exists.choose earned
  have report := Exists.choose_spec earned
  refine ⟨hid,?_⟩
  intro donor
  have nameFit : scalar<2^((ℒ).size+2):=by
    have bound:=(finProdFinEquiv (old_ (qAt raw),DescentCableDonorNames.role (raw).val)).isLt
    simp only [finProdFinEquiv_apply_val] at bound
    exact (by dsimp only [scalar];omega : scalar<(A).cap*11).trans_le ((Nat.mul_comm _ _).le.trans codeFit)
  exact returned_key_decoded ℒ old word_ grain nameRoom j h y prevPeer prevSerial piece read donor first second marked
    start dest _ _ (fun hit=>by simp [second,hit]) report ((halo.slot _ ⟨_,hid⟩).isLt.trans_le donorFit) nameFit


end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
