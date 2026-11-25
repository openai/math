import OAI.Hierarchy.DescentDatedSelectedCableKey
import OAI.Hierarchy.DescentDatedReturnedOldCable
import OAI.Hierarchy.DescentReachedCableOutcome
import OAI.Hierarchy.DescentRegisteredOldCableOrigin
import OAI.Hierarchy.DescentReachedBornCable
import OAI.Hierarchy.DescentRegisteredOldCableDigits
import OAI.Hierarchy.DescentReachedPhysicalBornHeader

namespace OAI
namespace Hierarchy.DescentOrdinaryBorn
open DescentSixParty DescentKernelHistory DescentOperandPhysicalInput DescentSIMDLookup
open DescentOperandStateBanks DescentRawCablePanel
open scoped Classical Fin.CommRing

private theorem registered_birth_cable_tag (B : Spec) (size z prof arg piece digit : ℕ) (party : Fin 6) (m : Mouth)
    (hit : mouth B z prof party arg = some m) (read : digit = (Pointer.cable 0 0 piece).header 0) :
    digit = (field B (size+2) 0 arg z prof party).val := by
  have room : (Pointer.cable 0 0 m.chunk).fields ⟨0,1,1⟩ 0 < 2^(size+2) := by
    change 1 < 2 ^ (size+2)
    exact (by decide : 1<2^2).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_left 2 size))
  rw [read, field_read B (size+2) 0 arg z prof party m hit room]
  rfl
end Hierarchy.DescentOrdinaryBorn

namespace Hierarchy.DescentLocalArchiveOrder
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.Chronology DescentStageEdgeReceipt
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentHostDirectory DescentHostDegree
open DescentPackedOperand DescentNetworkPartition
open scoped Classical
noncomputable section
set_option quotPrecheck false
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {c : (cap.placement.stage.result he).Choice}
    {n : Normalize ((cap.placement.stage.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he cap.placement.stage c n target) (arch : Archive W)
    (hp : 0<p) (one : 1≤R) (pin : ∀x,p∣bits x) (sh : WorldShape p R arch.bit) (unit : p∣cap.placement.stage.z)
local notation "T" => cap.placement.stage
local notation "r" => BitDescription.scannedRows he T
local notation "uni" => fun _ : (r).pairs=>(T).z
local notation "room" => fun _ : (r).pairs=>le_refl (T).z
local notation "whole" => fun _ : (r).pairs=>unit
local notation "prof" => (r).profile c
local notation "after" => afterOrdinary hp one pin ticket arch sh unit
local notation "M" => rawGraph he T c
local notation "baseShape" => physicalShape W arch.bit G (r).pick uni room prof hp sh.sites sh.edges pin whole
local notation "next" => (ticket.advance arch).bit
local notation "names" => NodeOrder.physicalNames arch.bit G (r).pick uni room prof
local notation:max "source" x:arg => operandSource ticket arch x


open DescentOrdinaryBorn DescentPackedOperand DescentCableDonorNames DescentPacking.PackedMatch.Local
local notation "A" => cap.placement

set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

attribute [local irreducible] BitDescription.scannedRows DescentPacking.slabPacking
private abbrev firstBirthMember (i : (r).pairs) : DescentSharedCableNames.Stage.Positive A :=
  let chosen := Stage.picked A he i.1 i.2 true
  ⟨chosen.val,(A).quantum_positive chosen.val chosen.property.1⟩


attribute [local irreducible] sourceIndex roots afterOrdinary GroupStage.stage StageInput.result
private abbrev BirthSourceEliminator : Prop :=
  ∀ (x:NodeOrder.All next) (j:Fin ((((after).sites x.1).recipe hp).arity x.2))
    (i:(r).pairs) (party:Fin 6) (_fresh:roots ticket arch x=.inr (i,party))
    (e:Incident (M) (source x).1) (piece:ℕ) (len:(piece+1)*p≤(M).width e.val)
    (_read:((baseShape (source x).1).recipe hp).operand (source x).2
      (sourceIndex ticket arch hp one pin sh unit x j)=.inl ⟨.inl e,piece,len⟩)
    (raw:DescentRawCablePanel.Live A (r).pick) (_same:raw.val=e.val) {C : Prop}
    (_consume:∀ o : Occurrence W G (r).pick uni prof p i party,
      (occurrences W G (r).pick uni prof p i party)[j.val]?=some o →
      let m:=occurrenceMouth W G (r).pick uni prof o
      let second:=decide (m.anchor.val=1)
      mouth (actual G p) (T).z (DescentPacking.PackedMatch.LayoutSum.profileCode G.C (prof i)).val party j.val=some m →
      piece=m.chunk → m.anchor.val=second.toNat → m.rawRole=(DescentCableDonorNames.role raw.val).val →
      Stage.CablePort A he (firstBirthMember (cap:=cap) (he:=he) i)
        (if second then 2 else 0) ⟨DescentCableDonorNames.anchor (r).pick raw.val,raw.property⟩ 0 → C), C
private theorem registered_newborn_source_apply : BirthSourceEliminator ticket arch hp one pin sh unit := by
  intro x j i party fresh e piece len read raw same C consume
  have readout := original_born_cable_source
    (cap:=cap) (he:=he) («T»:=cap.placement.stage) (c:=c) (n:=n) (target:=target)
    ticket arch hp one pin sh unit x j i party fresh e piece len read
  obtain ⟨o,found,hit,edge,chunk⟩ := readout
  have port := Stage.newborn_port A he i (occurrenceMouth W G (r).pick uni prof o) raw (same.trans edge)
  exact consume o found hit chunk port.1 port.2.1 port.2.2

end
end Hierarchy.DescentLocalArchiveOrder

namespace Hierarchy.DescentLocalArchiveOrder
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.Chronology DescentStageEdgeReceipt
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentHostDirectory DescentHostDegree
open DescentPackedOperand DescentNetworkPartition
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {q ε : ℝ} {S : AtomSchedule} {k i z D z' D' priorWire hist : ℕ}
    {cap : Reached W G q ε S k i z D priorWire hist}
    {he : 0≤ε} {c : (cap.placement.stage.result he).Choice}
    {n : Normalize ((cap.placement.stage.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' priorWire hist}
    (ticket : OrdinaryLink cap he cap.placement.stage c n target) (arch : Archive W)
    (hp : 0<p) (one : 1≤R) (pin : ∀x,p∣bits x) (sh : WorldShape p R arch.bit) (unit : p∣cap.placement.stage.z)
local notation "T" => cap.placement.stage
local notation "r" => BitDescription.scannedRows he T
local notation "uni" => fun _ : (r).pairs=>(T).z
local notation "pos" => fun _ : (r).pairs=>(T).unitPos
local notation "room" => fun _ : (r).pairs=>le_refl (T).z
local notation "whole" => fun _ : (r).pairs=>unit
local notation "prof" => (r).profile c
local notation "after" => afterOrdinary hp one pin ticket arch sh unit
local notation "M" => rawGraph he T c
local notation "baseShape" => physicalShape W arch.bit G (r).pick uni room prof hp sh.sites sh.edges pin whole
local notation "next" => (ticket.advance arch).bit
local notation "names" => NodeOrder.physicalNames arch.bit G (r).pick uni room prof
local notation "source" x:arg => (names).symm (roots ticket arch x)

open DescentPacking.PackedMatch.Local.Stage
local notation "args_" x:arg => (((after).sites (x:NodeOrder.All next).1).recipe hp).arity (x).2
local notation "input_" x:arg j:arg => ((baseShape (source x).1).recipe hp).operand (source x).2
    (sourceIndex ticket arch hp one pin sh unit x j)
local notation "anchor_" e:arg => DescentCableDonorNames.anchor (r).pick (e).val
local notation "live" => DescentRawCablePanel.Live cap.placement (r).pick
local notation "parent_" e:arg => (⟨anchor_ e,(e:live).property⟩:DescentSharedCableNames.Stage.Positive cap.placement)

set_option cleanup.letToHave false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
attribute [local irreducible] BitDescription.scannedRows DescentPacking.slabPacking
attribute [local irreducible] DescentLocalArchiveOrder.sourceIndex DescentLocalArchiveOrder.roots afterOrdinary GroupStage.stage StageInput.result
private abbrev SavedCableSourceEliminator : Prop :=
  ∀ (x:NodeOrder.All next) (j:Fin (args_ x)) (saved:NodeOrder.All arch.bit)
    (_origin:roots ticket arch x=.inl saved) (wire:Incident (M) (source x).1) (piece:ℕ)
    (fits:(piece+1)*p≤(M).width wire.val) (_read:input_ x j=.inl ⟨.inl wire,piece,fits⟩)
    {goal : Prop} (_useCable :
    let alive:=DescentPrivateRawLabels.parent_positive cap.placement S cap.valid (r).pick uni pos (r).fit prof hp
        (⟨wire.val,piece,((Nat.le_div_iff_mul_le hp).mpr fits)⟩:WireWord (M) p)
    let cable:live:=⟨wire.val,alive⟩
    ∀(s:Fin (((sh.sites saved.1).recipe hp).arity saved.2)) (oldWire:Incident W.graph saved.1)
        (oldFits:(piece+1)*p≤W.graph.width oldWire.val) (oldPositive:0<cap.placement.grainCount oldWire.val),
      s.val=j.val → ((sh.sites saved.1).recipe hp).operand saved.2 s=.inl ⟨.inl oldWire,piece,oldFits⟩ →
      CablePort cap.placement he ⟨oldWire.val,oldPositive⟩ (if W.graph.src oldWire.val=saved.1 then 0 else 1)
        (parent_ cable) (DescentCableDonorNames.role cable.val) → goal), goal

private theorem original_old_cable_elim : SavedCableSourceEliminator ticket arch hp one pin sh unit := by
  intro x j saved origin wire piece fits read goal useCable
  have receipt := original_old_cable (F:=F) (P:=P) (d:=d) (p:=p) (R:=R)
    (bits:=bits) (W:=W) (G:=G) (q:=q) (ε:=ε) (S:=S) (k:=k) (i:=i) (z:=z)
    (D:=D) (z':=z') (D':=D') (priorWire:=priorWire) (hist:=hist) (cap:=cap)
    (he:=he) (c:=c) (n:=n) (target:=target) ticket arch hp one pin sh unit
    x j saved origin wire piece fits read
  exact Exists.elim receipt fun slot more =>
    Exists.elim more fun edge more =>
      Exists.elim more fun valid more =>
        Exists.elim more fun isLive facts =>
          useCable slot edge valid isLive facts.1 facts.2.1 facts.2.2

end
end Hierarchy.DescentLocalArchiveOrder

/-! Cable tickets at occupied chronological nodes on the attained selected board. -/
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
set_option maxHeartbeats 360000
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
open DescentPackedOperand DescentOperandStateBanks DescentDatedPriorOperand
variable (old:Books v.withIssuedSigned.resolver) (grain:Cell (v.withIssuedSigned.resolver.size+2))
variable (orig : Fin v.withIssuedSigned.resolver.jobs→Fin 6→Values v.withIssuedSigned.ticketReadGeometry v.withIssuedSigned.operandShortBits)
    (born : Fin v.withIssuedSigned.resolver.jobs→Fin 3→Values v.withIssuedSigned.ticketReadGeometry v.withIssuedSigned.bornBook.bits)
local notation "prior" => fun j f h y=>booksHeader old j h y f
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
local notation "word_" => ticketAt Γ fixed_
local notation "side_" => fun j h y=>DescentDatedPublicGrain.withGrain grain (Ticket.recordedSide (ℒ).size (word_ j h y))
local notation "role_" => fun j f h y=>Ticket.recordedRole (ℒ).size (word_ j h y) f
variable (nameRoom:∀j h y,11*((fun j f h y=>Ticket.recordedRole v.withIssuedSigned.resolver.size (ticketAt v.withIssuedSigned.ticketReadGeometry (SortedInput.values v.withIssuedSigned.ticketReadGeometry (v.withIssuedSigned.originalValues (v.withIssuedSigned.sampleHeads bl hb gs orig (fun j f h y=>booksHeader old j h y f) born (v.withIssuedSigned.wideMaterialValues R B.material bands serial peer) (v.withIssuedSigned.narrowValue R))) (v.withIssuedSigned.walkValues (Gather.reaching R))) j h y) f) j 1 h y).val+((fun j f h y=>Ticket.recordedRole v.withIssuedSigned.resolver.size (ticketAt v.withIssuedSigned.ticketReadGeometry (SortedInput.values v.withIssuedSigned.ticketReadGeometry (v.withIssuedSigned.originalValues (v.withIssuedSigned.sampleHeads bl hb gs orig (fun j f h y=>booksHeader old j h y f) born (v.withIssuedSigned.wideMaterialValues R B.material bands serial peer) (v.withIssuedSigned.narrowValue R))) (v.withIssuedSigned.walkValues (Gather.reaching R))) j h y) f) j 2 h y).val<2^(v.withIssuedSigned.resolver.size+2))
local notation "jobs_" => decodedBooks old side_ role_ nameRoom


/-- The actual responding donor walk and its earlier book digits on the selected CPU. -/
def CableRoute (raw:live_) (piece:ℕ) : Prop :=
  ∃(path:Fin (breadth D)) (newborn:Bool) (prevPeer prevSerial:ℕ),
    Gather.select (Gather.reaching R) recv path=some (whereAt raw) ∧
    ((rawKey Γ fixed_ j h y).val=Ticket.socket path newborn (seatAt raw) ∧
      ticketAt Γ fixed_ j h y=actual_ path newborn raw) ∧
    ∀f,(booksHeader old j h y f).val=(Pointer.cable prevPeer prevSerial piece).header f

private abbrev observedCableReturn (raw : live_) (path : Fin (breadth D)) (isBorn : Bool) : Prop :=
  (rawKey Γ fixed_ j h y).val=Ticket.socket path isBorn (seatAt raw) ∧
    ticketAt Γ fixed_ j h y=actual_ path isBorn raw

open DescentBundleHistory DescentLocalArchiveOrder DescentNetworkPartition Computability.BorderVNP.Crossing
variable {lane stretch : ℕ} (archive : Archive v.world) (hp : 0 < lane) (one : 1 ≤ stretch)
    (pin : ∀ z, lane ∣ v.bits z) (sh : WorldShape lane stretch archive.bit) (unit : lane ∣ v.prior.placement.stage.z)
local notation "after₀" => afterOrdinary hp one pin (ac).link archive sh unit
local notation "next₀" => ((ac).link.advance archive).bit
local notation "units₀" => fun _:(rr).pairs=>(T).z
local notation "room₀" => fun _:(rr).pairs=>le_refl (T).z
local notation "atNode" x:arg => operandSource (ac).link archive x
local notation "base₀" => physicalShape v.world archive.bit G (rr).pick units₀ room₀ ((rr).profile selected)
    hp sh.sites sh.edges pin (fun _=>unit)
local notation "actualOperand" x:arg slot:arg => ((base₀ (operandSource (ac).link archive x).1).recipe hp).operand (atNode x).2
    (sourceIndex (ac).link archive hp one pin sh unit x slot)
variable (x : NodeOrder.All (((atSelected v selected choiceEq).link).advance archive).bit)
    (arg : Fin ((((afterOrdinary hp one pin (atSelected v selected choiceEq).link archive sh unit).sites x.1).recipe hp).arity x.2))
    (wire : Incident (rawGraph v.nonnegative v.prior.placement.stage selected) (operandSource (atSelected v selected choiceEq).link archive x).1)
    (piece : ℕ) (length : (piece+1)*lane ≤ (rawGraph v.nonnegative v.prior.placement.stage selected).width wire.val)
local notation "positive" => DescentPrivateRawLabels.parent_positive A S v.prior.valid (rr).pick units₀
    (fun _=>(T).unitPos) (rr).fit ((rr).profile selected) hp
    (⟨wire.val,piece,(Nat.le_div_iff_mul_le hp).mpr length⟩:WireWord (net_) lane)
private abbrev physicalReachedCable : live_ := ⟨wire.val,positive⟩
local notation "cable" => physicalReachedCable (v:=v) (selected:=selected) (choiceEq:=choiceEq) (archive:=archive) (hp:=hp) (x:=x) (wire:=wire) (piece:=piece) (length:=length)
variable (listed : ∀ u t, t ∈ v.prior.placement.near u →
      ∃ i, R ((v.prior.vertex.trans (Fin.castLEEmb oldFit)) u) i = some ((v.prior.vertex.trans (Fin.castLEEmb oldFit)) t))
    (agrees : ∀ u i, R ((v.prior.vertex.trans (Fin.castLEEmb oldFit)) u) i =
      (hostRotor (v.prior.vertex.trans (Fin.castLEEmb oldFit))
        (DescentGroupPeerOrder.hostRoster v.prior.placement ((v.prior.vertex.trans (Fin.castLEEmb oldFit)).trans Fin.valEmbedding))) ((v.prior.vertex.trans (Fin.castLEEmb oldFit)) u) i)
    (symmetric : ∀ u t i, R u i = some t → ∃ z, R t z = some u)
    (donorFit : breadth v.prior.placement.degree * 2^v.k ≤ 2^(v.withIssuedSigned.resolver.size+2))
    (codeFit : 11*v.prior.placement.cap ≤ 2^(v.withIssuedSigned.resolver.size+2))
local notation "result₀" => CableOutcome (ac).link archive hp one pin sh unit hosts R listed x arg wire piece length
    (resolve (((jobs_) j).compiled h y))

set_option maxHeartbeats 1200000 in
include agrees symmetric donorFit codeFit in
/-- Decode a measured socket on this particular physical board.  The public
peer and serial come from its signed row at this same job, host and group. -/
private theorem registeredCableAtProof (path:Fin (breadth D)) (isBorn:Bool)
    (ticketRead : observedCableReturn (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected)
      (m:=m) (parts:=parts) (B:=B) (bl:=bl) (hb:=hb) (gs:=gs) (bands:=bands)
      (serial:=serial) (peer:=peer) (old:=old) (orig:=orig) (born:=born) (j:=j) (h:=h) (y:=y) cable path isBorn)
    (prevPeer prevSerial:ℕ)
    (priorRead:∀f,(booksHeader old j h y f).val=(Pointer.cable prevPeer prevSerial piece).header f) :
    result₀ :=by
  have pieceFit:piece<2^((ℒ).size+2):=(priorRead 3).ge.trans_lt (booksHeader old j h y 3).isLt
  have issued:=returned_cable_key_decoded (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected)
    (m:=m) (parts:=parts) (B:=B) (bl:=bl) (hb:=hb) (gs:=gs) (bands:=bands)
    (serial:=serial) (peer:=peer) (orig:=orig) («prior»:=prior) (born:=born)
    (j:=j) (h:=h) (y:=y) (choiceEq:=choiceEq) (old:=old) (grain:=grain)
    (nameRoom:=nameRoom) path isBorn cable ticketRead listed agrees symmetric
    prevPeer prevSerial piece priorRead donorFit codeFit
  exact CableOutcome.of_dated (name:=hosts) (roster:=R) (listed:=listed)
    (piece:=piece) (full:=length) (key:=resolve (((jobs_) j).compiled h y)) (arch:=archive) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh)
    (receipt:=(ac).link) (alignedGrains:=unit) (x:=x) (j:=arg) (e:=wire) (size:=(ℒ).size)
    (((fixed_).raw j 7 (row_ path cable) h y).val:Cell ((ℒ).size+2))
    (((fixed_).raw j 6 (row_ path cable) h y).val:Cell ((ℒ).size+2)) grain pieceFit issued


private abbrev RegisteredCableAtStatement : Prop := type_of% @registeredCableAtProof

/-- Decode the registered socket on the selected physical board. -/
theorem registered_cable_at : RegisteredCableAtStatement := @registeredCableAtProof

private abbrev actualReceiverForColumn (raw : live_) (side : Bool) : Fin H :=
  hosts ((if side then own_ (GadgetNetwork.newSite
  v.world.graph (rr).pick lay pack_ (GadgetNetwork.target v.world.graph (rr).pick (raw).val))
  else own_ (zone_ raw)).1).2
local notation "nativeReceiver" raw:arg side:arg => actualReceiverForColumn (v:=v) (oldFit:=oldFit)
  (selected:=selected) (choiceEq:=choiceEq) raw side



local notation "route₀" => CableRoute (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected)
  (m:=m) (parts:=parts) (B:=B) (bl:=bl) (hb:=hb) (gs:=gs) (bands:=bands) (serial:=serial) (peer:=peer)
  (orig:=orig) (old:=old) (born:=born) (j:=j) (h:=h) (y:=y) (recv:=recv) cable piece
local notation "basis₀" => privateChart (ac).link archive hp one pin sh unit
local notation "address₀" => MarkedWorld.address (scanWorld v.nonnegative T selected)
  ((basis₀).key v.nonnegative T selected) (basis₀).hub (T).k (gainExponent 20 (T).Δ)
local notation "toZone" => GadgetNetwork.newSite v.world.graph (rr).pick lay (rr).pack
local notation "publicMark" => DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role wire.val)
  (decide (DescentCableDonorNames.anchor (rr).pick wire.val∈v.world.core))

set_option maxHeartbeats 950000 in
include listed agrees symmetric donorFit codeFit in
/-- When both endpoint owners remain distinct, the same donated path that read the
registered ticket supplies fields 7 and 6 to the public fragment. -/
private theorem survivingCableProof (measured:route₀)
    (distinct:address₀ (toZone ((net_).src wire.val))≠address₀ (toZone ((net_).dst wire.val))) :
    ∃(path:Fin (breadth D)) (fit:piece<2^((ℒ).size+2)),
      Gather.select (Gather.reaching R) recv path=some (whereAt cable) ∧
      resolve (((jobs_) j).compiled h y)=resolve (Public.fragment publicMark
        (((fixed_).raw j 7 (row_ path cable) h y).val:Cell ((ℒ).size+2))
        (((fixed_).raw j 6 (row_ path cable) h y).val:Cell ((ℒ).size+2)) ⟨piece,fit⟩ grain) :=by
  obtain ⟨path,fresh,neighbor,wireNo,hit,recorded,previous⟩:=measured
  have issued := returned_cable_key_decoded (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected)
    (m:=m) (parts:=parts) (B:=B) (bl:=bl) (hb:=hb) (gs:=gs) (bands:=bands) (serial:=serial)
    (peer:=peer) (orig:=orig) («prior»:=prior) (born:=born) (old:=old) (grain:=grain) (j:=j)
    (h:=h) (y:=y) (choiceEq:=choiceEq) (nameRoom:=nameRoom) path fresh cable recorded
    listed agrees symmetric neighbor wireNo piece previous donorFit codeFit
  have rawRead:=Exists.choose_spec issued
  have sides:=source_owners (ac).link archive hp one pin sh unit ((net_).src wire.val) ((net_).dst wire.val)
  have separate:oldSite_ ((net_).src wire.val)≠oldSite_ ((net_).dst wire.val):=
    fun same=>distinct (congrArg address₀ (sides.1.mp same))
  have stays:owner_ ((net_).src wire.val)≠owner_ ((net_).dst wire.val):=fun same=>distinct (sides.2.mp same)
  refine ⟨path,(previous 3).ge.trans_lt (booksHeader old j h y 3).isLt,hit,?_⟩
  simp only [decide_eq_false separate,decide_eq_false stays,Bool.not_false,Bool.true_and,Bool.false_eq_true,ite_false] at rawRead
  exact rawRead

private abbrev SurvivingCableStatement : Prop := type_of% @survivingCableProof

/-- A surviving route supplies the signed public fragment from its donor's stored fields. -/
theorem CableRoute.surviving : SurvivingCableStatement := @survivingCableProof

set_option maxHeartbeats 1500000 in
/-- The receiver and dense W coordinates before signed-route selection. The predecessor
signed planes are shared across all these rows; both routing walks are computed from them. -/
structure OldCableColumns (site:v.world.graph.Site) (raw:live_) where
  side : Bool
  ordinal : Fin (breadth D)
  atOwner : recv=nativeReceiver raw side
  cohort : grpAt=((A).pos site).1
  cause : (orig j 0 h y).val=1
  stamp : (orig j 1 h y).val=ordinal.val
  sorted : DescentSortedRoster.indexed (Gather.reaching R) recv ordinal=some (hosts ((A).pos site).2)
  block : (orig j 2 h y).val=((A).block site).val

/-- The real one-based newborn W stamp and its three stored mouth words. -/
structure BornCableColumns (q:pos_) (party:Fin 6) (mouth:DescentOrdinaryBorn.Mouth) where
  chart : Return
  ordinal : Fin (breadth chart.degree)
  block : Fin (2^chart.depth)
  seat : Fin chart.capacity
  node : Fin chart.newNodes
  word : Cell (chart.ordinalBits*chart.newNodes)
  index : Fin (breadth D)
  stamp : ((encode chart.ordinalBits chart.newNodes).symm word node).val=
    (candidate chart ordinal block (.inr (seat,party))).val+1
  origin : ∀f,orig j f h y=readLaw chart (Γ).digitBits node f word
  ordinalId : ordinal.val=index.val
  blockId : block.val=(block_ q).val
  seatId : seat.val=(old_ q).val
  digitRoom : max 2 (max ordinal.val (max block.val seat.val))<2^(Γ).digitBits
  sorted : DescentSortedRoster.indexed (Gather.reaching R) recv index=some (hosts ((A).pos (from_ q)).2)
  cohort : grpAt=((A).pos (from_ q)).1
  ports : ∀f,(born j f h y).val=(DescentOrdinaryBorn.RolePorts.value (phys).bornBook.bits (some mouth) f).val


local notation "oldCols" site:arg raw:arg =>
  OldCableColumns (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected) (choiceEq:=choiceEq)
    (bl:=bl) (gs:=gs) (bands:=bands) (orig:=orig) (j:=j) (h:=h) (y:=y) (recv:=recv) site raw
local notation "bornCols" q:arg party:arg mouth:arg =>
  BornCableColumns (v:=v) (oldFit:=oldFit) (R:=R) (bl:=bl) (gs:=gs) (bands:=bands)
    (orig:=orig) (born:=born) (j:=j) (h:=h) (y:=y) (recv:=recv) q party mouth
local notation "oldEndpt" saved:arg edge:arg live:arg =>
  DescentSharedCableNames.Stage.live A native S v.prior.valid (Stage.cableNames v.k rank)
    (DescentSharedCableNames.Stage.home A (saved).1) (DescentTerminalPortChart.first A (saved).1 edge live)
local notation "signedBoard" => Prepare.signed A native S v.prior.valid (grp).toEmbedding hosts
private abbrev registeredFirstMember (pair : (rr).pairs) : pos_ :=
  let chosen := Stage.picked A v.nonnegative pair.1 pair.2 true
  ⟨chosen.val,(A).quantum_positive chosen.val chosen.property.1⟩
local notation "first₀" pair:arg => registeredFirstMember v pair
local notation "birthMouth" o:arg => DescentOrdinaryBorn.occurrenceMouth v.world G (rr).pick units₀ ((rr).profile selected) o
local notation "profileAt" pair:arg => (DescentPacking.PackedMatch.LayoutSum.profileCode (G).C (((rr).profile selected) pair)).val
local notation "savedRoot" => roots (ac).link archive x

local notation "wingAt" site:arg edge:arg live:arg =>
  DescentSharedCableNames.Stage.live A native S v.prior.valid (Stage.cableNames v.k rank)
    (DescentSharedCableNames.Stage.home A site) (DescentTerminalPortChart.first A site edge live)
set_option cleanup.letToHave false
set_option maxHeartbeats 1600000 in
include atHost in
private theorem saved_socket_from_frame
    (originalR : R=canon_) (site : v.world.graph.Site) (edge : Incident v.world.graph site)
    (live : 0 < (A).grainCount edge.val) (raw : live_) (chunk : ℕ)
    (port : Stage.CablePort A v.nonnegative (⟨edge.val,live⟩ : pos_)
      (if v.world.graph.src edge.val=site then 0 else 1) (qAt raw) (DescentCableDonorNames.role raw.val))
    (frame : oldCols site raw)
    (digits : let wing := wingAt site edge live
      ∀f,(booksHeader old j h y f).val=(Pointer.cable wing.neighbor.val wing.wire.val chunk).header f) :
    CableRoute (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected)
      (m:=m) (parts:=parts) (B:=B) (bl:=bl) (hb:=hb) (gs:=gs) (bands:=bands) (serial:=serial) (peer:=peer)
      (orig:=orig) (old:=old) (born:=born) (j:=j) (h:=h) (y:=y) (recv:=recv) raw chunk := by
  let wing := wingAt site edge live
  have material := returned_old_socket_material v oldFit R selected m parts B bl hb gs bands serial peer orig prior born
    j h y recv atHost (ac).link.donorChart.same originalR site edge live raw frame.side port
    frame.atOwner frame.cohort frame.ordinal chunk frame.cause frame.stamp frame.sorted frame.block digits
  obtain ⟨path,visited,issued⟩ := material
  exact ⟨path,false,wing.neighbor.val,wing.wire.val,visited,issued,digits⟩


local notation "formedRoute" raw:arg digit:arg => CableRoute (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected)
  (m:=m) (parts:=parts) (B:=B) (bl:=bl) (hb:=hb) (gs:=gs) (bands:=bands) (serial:=serial) (peer:=peer)
  (orig:=orig) (old:=old) (born:=born) (j:=j) (h:=h) (y:=y) (recv:=recv) raw digit
local notation "frameAt" q:arg party:arg mouth:arg =>
  BornCableColumns (v:=v) (oldFit:=oldFit) (R:=R) (bl:=bl) (gs:=gs) (bands:=bands)
    (orig:=orig) (born:=born) (j:=j) (h:=h) (y:=y) (recv:=recv) q party mouth

set_option maxHeartbeats 1000000 in
include atHost in
private theorem registered_born_port_route (q : pos_) (raw : live_) (second : Bool)
    (piece : ℕ) (party : Fin 6) (basis : DescentOrdinaryBorn.Spec) (slot scale prof : ℕ)
    (mouth : DescentOrdinaryBorn.Mouth)
    (hit : DescentOrdinaryBorn.mouth basis scale prof party slot = some mouth)
    (mouthRoom : 11 ≤ 2^(phys).bornBook.bits)
    (digits : ∀f, (booksHeader old j h y f).val=(Pointer.cable 0 0 piece).header f)
    (frame : frameAt q party mouth)
    (side : mouth.anchor.val=second.toNat)
    (role : mouth.rawRole=(DescentCableDonorNames.role raw.val).val)
    (port : Stage.CablePort A v.nonnegative q (if second then 2 else 0) (qAt raw) 0) :
    formedRoute raw piece := by
  have tag := DescentOrdinaryBorn.registered_birth_cable_tag basis (ℒ).size scale prof slot piece _ party mouth hit (digits 0)
  obtain ⟨path, visited, observed⟩ := returned_birth_socket v oldFit R selected m parts B bl hb gs bands serial peer orig prior born
    j h y recv atHost q raw second port frame.chart frame.ordinal frame.block frame.seat party frame.node frame.word
    frame.stamp frame.origin frame.index frame.ordinalId frame.blockId frame.seatId frame.digitRoom frame.sorted frame.cohort
    basis slot scale prof mouth hit mouthRoom tag frame.ports side role
  exact ⟨path,true,0,0,visited,observed,digits⟩

private theorem registeredRouteCases {α β γ : Type*} (sourceCase : α ⊕ (β × γ)) {conclusion : Prop}
    (left : ∀ a, sourceCase = .inl a → conclusion) (right : ∀ b c, sourceCase = .inr (b,c) → conclusion) : conclusion := by
  cases sourceCase with
  | inl a => exact left a rfl
  | inr pair => exact right pair.1 pair.2 rfl

set_option maxHeartbeats 1000000 in
include agrees symmetric donorFit codeFit in
private theorem registered_finish_route (measured : route₀) : result₀ ∧ route₀ := by
  refine ⟨?_, measured⟩
  obtain ⟨path, isBorn, prev, start, _, observed, saved⟩ := measured
  exact registered_cable_at (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected) (m:=m) (parts:=parts)
      (B:=B) (bl:=bl) (hb:=hb) (gs:=gs) (bands:=bands) (serial:=serial) (peer:=peer)
      (old:=old) (grain:=grain) (orig:=orig) (born:=born) (j:=j) (h:=h) (y:=y)
      (choiceEq:=choiceEq) (nameRoom:=nameRoom) (archive:=archive) (hp:=hp) (one:=one) (pin:=pin)
      (sh:=sh) (unit:=unit) (x:=x) (arg:=arg) (wire:=wire) (piece:=piece) (length:=length)
      (listed:=listed) (agrees:=agrees) (symmetric:=symmetric) (donorFit:=donorFit) (codeFit:=codeFit)
      path isBorn observed prev start saved

section
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
attribute [local irreducible] DescentLocalArchiveOrder.sourceIndex DescentLocalArchiveOrder.roots BitDescription.scannedRows afterOrdinary GroupStage.stage StageInput.result
set_option maxHeartbeats 1250000 in
private abbrev BornSourceRouteStatement : Prop :=
  ∀
    (_read:actualOperand x arg=.inl ⟨.inl wire,piece,length⟩)
    (_mouthRoom:11≤2^(phys).bornBook.bits) (_originalR:R=canon_)
    (_bornPages:∀(pair:(rr).pairs) (party:Fin 6),savedRoot=.inr (pair,party)→
      ∀o:DescentOrdinaryBorn.Occurrence v.world G (rr).pick units₀ ((rr).profile selected) lane pair party,
        (DescentOrdinaryBorn.occurrences v.world G (rr).pick units₀ ((rr).profile selected) lane pair party)[arg.val]?=some o→
        let mouth:=birthMouth o
        DescentOrdinaryBorn.mouth (DescentOrdinaryBorn.actual G lane) (T).z (profileAt pair) party arg.val=some mouth→
        piece=mouth.chunk→
        (∀f,(booksHeader old j h y f).val=(Pointer.cable 0 0 piece).header f) ∧
          Nonempty (bornCols (first₀ pair) party mouth))
    (pair : (rr).pairs) (party : Fin 6) (_origin : savedRoot=.inr (pair,party)), route₀
include atHost in
private theorem registered_born_step : BornSourceRouteStatement (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected) (m:=m) (parts:=parts) (B:=B) (bl:=bl) (hb:=hb) (gs:=gs) (bands:=bands) (serial:=serial) (peer:=peer) (orig:=orig) (old:=old) (born:=born) (j:=j) (h:=h) (y:=y) (recv:=recv) (choiceEq:=choiceEq) (archive:=archive) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit) (x:=x) (arg:=arg) (wire:=wire) (piece:=piece) (length:=length) := by
  intro read mouthRoom originalR bornPages pair party origin
  refine registered_newborn_source_apply (cap:=v.prior) (he:=v.nonnegative) (c:=selected)
    (n:=(ac).norm) (target:=(ac).next) (ac).link archive hp one pin sh unit x arg pair party origin
    wire piece length read cable rfl (fun occ found hit chunk side role port => ?_)
  obtain ⟨digits,⟨frame⟩⟩:=bornPages pair party origin occ found hit chunk
  exact registered_born_port_route (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected)
    (m:=m) (parts:=parts) (B:=B) (bl:=bl) (hb:=hb) (gs:=gs) (bands:=bands) (serial:=serial) (peer:=peer)
    (old:=old) (orig:=orig) (born:=born) (j:=j) (h:=h) (y:=y) (recv:=recv) (atHost:=atHost)
    (first₀ pair) cable (decide ((birthMouth occ).anchor.val=1)) piece party (DescentOrdinaryBorn.actual G lane)
    arg.val (T).z (profileAt pair) (birthMouth occ) hit mouthRoom digits frame side role port


end

section
set_option cleanup.letToHave false
set_option maxHeartbeats 1600000 in
include atHost in
private theorem saved_socket_from_page
    (originalR : R=canon_) (site : v.world.graph.Site) (edge : Incident v.world.graph site)
    (live : 0 < (A).grainCount edge.val) (raw : live_) (chunk : ℕ)
    (port : Stage.CablePort A v.nonnegative (⟨edge.val,live⟩ : pos_)
      (if v.world.graph.src edge.val=site then 0 else 1) (qAt raw) (DescentCableDonorNames.role raw.val))
    (page : let wing := wingAt site edge live
      (∀f,(booksHeader old j h y f).val=(Pointer.cable wing.neighbor.val wing.wire.val chunk).header f)
      ∧ Nonempty (oldCols site raw)) :
    CableRoute (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected)
      (m:=m) (parts:=parts) (B:=B) (bl:=bl) (hb:=hb) (gs:=gs) (bands:=bands) (serial:=serial) (peer:=peer)
      (orig:=orig) (old:=old) (born:=born) (j:=j) (h:=h) (y:=y) (recv:=recv) raw chunk := by
  exact page.2.elim fun frame =>
    saved_socket_from_frame (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected) (m:=m) (parts:=parts)
      (B:=B) (bl:=bl) (hb:=hb) (gs:=gs) (bands:=bands) (serial:=serial) (peer:=peer)
      (old:=old) (orig:=orig) (born:=born) (j:=j) (h:=h) (y:=y) (recv:=recv)
      (atHost:=atHost) (choiceEq:=choiceEq) originalR site edge live raw chunk port frame page.1


attribute [local irreducible] DescentLocalArchiveOrder.roots DescentLocalArchiveOrder.sourceIndex afterOrdinary
set_option cleanup.letToHave false
set_option Elab.async false
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
attribute [local irreducible] BitDescription.scannedRows DescentPacking.slabPacking
set_option maxHeartbeats 2200000
attribute [local irreducible] GroupStage.stage StageInput.result
private abbrev SavedPhysicalRoute : Prop :=
  ∀ (_read:actualOperand x arg=.inl ⟨.inl wire,piece,length⟩)
    (_originalR:R=canon_)
    (_oldPages:∀(saved:NodeOrder.All archive.bit),savedRoot=.inl saved→
      ∀(slot:Fin (((sh.sites saved.1).recipe hp).arity saved.2)) (edge:Incident v.world.graph saved.1)
        (valid:(piece+1)*lane≤v.world.graph.width edge.val) (live:0<(A).grainCount edge.val),
        slot.val=arg.val→((sh.sites saved.1).recipe hp).operand saved.2 slot=.inl ⟨.inl edge,piece,valid⟩→
        let wing:=oldEndpt saved edge live
        (∀f,(booksHeader old j h y f).val=(Pointer.cable wing.neighbor.val wing.wire.val piece).header f) ∧
          Nonempty (oldCols saved.1 cable))
    (saved : NodeOrder.All archive.bit) (_origin : savedRoot=.inl saved), route₀
include atHost in
private theorem registered_route_from_saved :
    SavedPhysicalRoute (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected)
      (m:=m) (parts:=parts) (B:=B) (bl:=bl) (hb:=hb) (gs:=gs) (bands:=bands)
      (serial:=serial) (peer:=peer) (old:=old) (orig:=orig) (born:=born) (j:=j)
      (h:=h) (y:=y) (recv:=recv) (choiceEq:=choiceEq) (archive:=archive) (hp:=hp)
      (one:=one) (pin:=pin) (sh:=sh) (unit:=unit) (x:=x) (arg:=arg) (wire:=wire)
      (piece:=piece) (length:=length) := by
  intro read originalR oldPages saved origin
  refine original_old_cable_elim (F:=F) (P:=P) (d:=v.dimension) (p:=lane) (R:=stretch)
    (bits:=v.bits) (W:=v.world) («G»:=v.gadget) (q:=v.q) (ε:=v.ε)
    («S»:=v.schedule) (k:=v.k) (i:=v.age) (z:=v.z) («D»:=v.degree)
    (z':=v.nextZ) (D':=v.nextDegree) (priorWire:=v.wire) (hist:=v.hist) (cap:=v.prior) (he:=v.nonnegative) (c:=selected)
    (n:=(ac).norm) (target:=(ac).next) (ac).link archive hp one pin sh unit
    x arg saved origin wire piece length read (goal:=route₀) ?_
  intro _positive _retainedWire slot edge valid isLive num oldRead port
  have received := oldPages saved origin slot edge valid isLive num oldRead
  exact saved_socket_from_page (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected) (m:=m) (parts:=parts)
    (B:=B) (bl:=bl) (hb:=hb) (gs:=gs) (bands:=bands) (serial:=serial) (peer:=peer)
    (old:=old) (orig:=orig) (born:=born) (j:=j) (h:=h) (y:=y) (recv:=recv)
    (atHost:=atHost) (choiceEq:=choiceEq) originalR saved.1 edge isLive cable piece port received

end

private abbrev RegisteredCableInputs (conclusion : Prop) : Prop :=
  ∀
    (_read:actualOperand x arg=.inl ⟨.inl wire,piece,length⟩)
    (_mouthRoom:11≤2^(phys).bornBook.bits) (_originalR:R=canon_)
    (_oldPages:∀(saved:NodeOrder.All archive.bit),savedRoot=.inl saved→
      ∀(slot:Fin (((sh.sites saved.1).recipe hp).arity saved.2)) (edge:Incident v.world.graph saved.1)
        (valid:(piece+1)*lane≤v.world.graph.width edge.val) (live:0<(A).grainCount edge.val),
        slot.val=arg.val→((sh.sites saved.1).recipe hp).operand saved.2 slot=.inl ⟨.inl edge,piece,valid⟩→
        let wing:=oldEndpt saved edge live
        (∀f,(booksHeader old j h y f).val=(Pointer.cable wing.neighbor.val wing.wire.val piece).header f) ∧
          Nonempty (oldCols saved.1 cable))
    (_bornPages:∀(pair:(rr).pairs) (party:Fin 6),savedRoot=.inr (pair,party)→
      ∀o:DescentOrdinaryBorn.Occurrence v.world G (rr).pick units₀ ((rr).profile selected) lane pair party,
        (DescentOrdinaryBorn.occurrences v.world G (rr).pick units₀ ((rr).profile selected) lane pair party)[arg.val]?=some o→
        let mouth:=birthMouth o
        DescentOrdinaryBorn.mouth (DescentOrdinaryBorn.actual G lane) (T).z (profileAt pair) party arg.val=some mouth→
        piece=mouth.chunk→
        (∀f,(booksHeader old j h y f).val=(Pointer.cable 0 0 piece).header f) ∧
          Nonempty (bornCols (first₀ pair) party mouth)), conclusion

set_option maxHeartbeats 1600000 in
include atHost agrees symmetric donorFit codeFit in
/-- Each real source operand uses its own dated old or newborn registers. The old edge, its
side, the newborn mouth and the two contractions' common donor are determined by the selected
semantic operand, before the physical matcher is run. -/
private theorem registered_cable_route_proof : RegisteredCableInputs (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected) (bl:=bl) (gs:=gs) (bands:=bands) (orig:=orig) (old:=old) (born:=born) (j:=j) (h:=h) (y:=y) (recv:=recv) (choiceEq:=choiceEq) (archive:=archive) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit) (x:=x) (arg:=arg) (wire:=wire) (piece:=piece) (length:=length) (result₀ ∧ route₀) := by
  intro read mouthRoom originalR oldPages bornPages
  refine registered_finish_route (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected)
    (m:=m) (parts:=parts) (B:=B) (bl:=bl) (hb:=hb) (gs:=gs) (bands:=bands)
    (serial:=serial) (peer:=peer) (old:=old) (orig:=orig) (born:=born)
    (j:=j) (h:=h) (y:=y) (recv:=recv) (choiceEq:=choiceEq)
    (archive:=archive) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit)
    (x:=x) (arg:=arg) (wire:=wire) (piece:=piece) (length:=length) (grain:=grain) (nameRoom:=nameRoom)
    (listed:=listed) (agrees:=agrees) (symmetric:=symmetric) (donorFit:=donorFit) (codeFit:=codeFit) ?_
  refine registeredRouteCases savedRoot ?_ ?_
  · exact registered_route_from_saved (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected)
      (m:=m) (parts:=parts) (B:=B) (bl:=bl) (hb:=hb) (gs:=gs) (bands:=bands)
      (serial:=serial) (peer:=peer) (old:=old) (orig:=orig) (born:=born)
      (j:=j) (h:=h) (y:=y) (recv:=recv) (choiceEq:=choiceEq)
      (archive:=archive) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit)
      (x:=x) (arg:=arg) (wire:=wire) (piece:=piece) (length:=length) (atHost:=atHost) read originalR oldPages
  · exact registered_born_step (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected)
      (m:=m) (parts:=parts) (B:=B) (bl:=bl) (hb:=hb) (gs:=gs) (bands:=bands)
      (serial:=serial) (peer:=peer) (old:=old) (orig:=orig) (born:=born)
      (j:=j) (h:=h) (y:=y) (recv:=recv) (choiceEq:=choiceEq)
      (archive:=archive) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit)
      (x:=x) (arg:=arg) (wire:=wire) (piece:=piece) (length:=length) (atHost:=atHost) read mouthRoom originalR bornPages

set_option maxHeartbeats 1600000 in
include atHost agrees symmetric donorFit codeFit in
private theorem registered_cable_jobs_proof : RegisteredCableInputs (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected) (bl:=bl) (gs:=gs) (bands:=bands) (orig:=orig) (old:=old) (born:=born) (j:=j) (h:=h) (y:=y) (recv:=recv) (choiceEq:=choiceEq) (archive:=archive) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit) (x:=x) (arg:=arg) (wire:=wire) (piece:=piece) (length:=length) result₀ := by
  intro read mouthRoom originalR oldPages bornPages
  exact (registered_cable_route_proof (v:=v) (oldFit:=oldFit) (R:=R) (selected:=selected)
    (m:=m) (parts:=parts) (B:=B) (bl:=bl) (hb:=hb) (gs:=gs) (bands:=bands)
    (serial:=serial) (peer:=peer) (old:=old) (grain:=grain) (orig:=orig) (born:=born)
    (j:=j) (h:=h) (y:=y) (recv:=recv) (atHost:=atHost) (choiceEq:=choiceEq) (nameRoom:=nameRoom)
    (archive:=archive) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit) (x:=x) (arg:=arg)
    (wire:=wire) (piece:=piece) (length:=length) (listed:=listed) (agrees:=agrees)
    (symmetric:=symmetric) (donorFit:=donorFit) (codeFit:=codeFit) read mouthRoom originalR oldPages bornPages).1

private abbrev RegisteredCableRouteStatement : Prop := type_of% @registered_cable_route_proof
private abbrev RegisteredCableJobsStatement : Prop := type_of% @registered_cable_jobs_proof

/-- The earlier or newborn source supplies the selected cable route and its physical result. -/
theorem registered_cable_route : RegisteredCableRouteStatement := @registered_cable_route_proof

/-- The stored socket and signed predecessor produce the result for the selected cable. -/
theorem registered_cable_jobs : RegisteredCableJobsStatement := @registered_cable_jobs_proof

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
