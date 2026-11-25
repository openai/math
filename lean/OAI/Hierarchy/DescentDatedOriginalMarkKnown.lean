import OAI.Hierarchy.DescentDatedOriginalMeasuredShelf
import OAI.Hierarchy.DescentOrdinaryPaidMarkHosts

namespace OAI
/-! # The previous signed wire supplies the mark on the actual measured parent roster. -/
namespace Hierarchy.DescentOrdinarySignedMeta
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.MarkedWorld DescentCableDonorNames DescentHostDirectory DescentColonies
open DescentStageEdgeReceipt GadgetNetwork DescentSharedCableNames
open scoped Classical Fin.CommRing
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k age : ℕ} {bits : P → ℕ} (W : MarkedWorld F d P bits) (G : PoweredGadget F)
    {price ε : ℝ} (A : GroupStage W G price ε J V k) (native : W.graph.Edge ↪ ℕ)
    (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S age) (rank : (J × V) ↪ ℕ)
private theorem donorPanel_relabel {hosts previous current : ℕ} (lookup : Fin hosts → Option V)
    (parent : Fin previous → J) (lane : Fin current → Fin previous) :
    (fun o h j => donorPanel W G A native S ready rank lookup parent o h (lane j)) =
      donorPanel W G A native S ready rank lookup (fun j => parent (lane j)) := rfl
end
end Hierarchy.DescentOrdinarySignedMeta

namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {k i z D wire hist w short a : ℕ}
variable {W : MarkedWorld F d P bits} {prior : Reached W G q ε S k i z D wire hist}
set_option maxHeartbeats 1100000
attribute [local irreducible] Stage.nativeParts physicalRows DepotRAM.chip packDonor StarKeys.nativeKey OrdinaryLink.donorKey OrdinaryLink.measuredDonors
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
local notation "rr" => BitDescription.scannedRows he T
local notation "lay" => bestLayout (branchWidth G (fun _ : (rr).pairs=>(T).z) ((rr).profile choice))
local notation "bytes" => donorNameBits (T).k (T).Δ
local notation "slots" => 2^(packExponent 20 (T).Δ)+2
local notation "gain" => gainExponent 20 (T).Δ
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
local notation "oldPorts" => S.groupCount i*(2^k)*(A).cap

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

local notation "N" => rawGraph he T choice
local notation "owner" => rawOwner he T choice n ((rr).state choice) (originalId _)
local notation "positiveRows" => DescentRawCablePanel.Live A (rr).pick
local notation:max "units" h:arg j:arg => liveMass (report (T).k gain slots
  (DepotRAM.seatDonor fmt profile G.b slots (measured h (groupSeat j).1) (groupSeat j).2.1 (groupSeat j).2.2.1)
  (groupSeat j).2.2.2)

open DescentSharedCableNames DescentHaloPackedRebase DescentParallelBase.ParentFilter
local notation "homeAt" => newSite W.graph (rr).pick lay (rr).pack
local notation:max "ctr" e:arg => mergeHub ticket.donorHub (T).k gain (ticket.donorKey (homeAt e))
local notation "P₀" => breadth (A).degree
local notation "Q" => 2^((T).k+1)*slots
local notation "K₀" => (P₀+1)*DepotRAM.Material.roles fmt
local notation "pitch" => (2^((T).k+1)-1)*slots
variable (fieldBits : ℕ)
local notation "form" => rawFormat (G:=G) (prior:=prior) profile pitch fieldBits
local notation "roomAt" => original_parent_room ticket port win hm named fit winner df order profile b m sumSize stored
                            dest issued roster mounted birth pitch fieldBits roster
local notation:max "rev" h:arg => digest (DepotRAM.Material.reverseEntries fmt roster h)

local notation:max "cell" h:arg j:arg => originalRecord ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch fieldBits h (groupSeat j).1 (groupSeat j).2
local notation:max "current" x:arg => n.destination (rawInput he T choice ((rr).state choice) x)
local notation:max "venue" x:arg => ticket.parentVenue port.enough (next.placement.pos (current x)).2
local notation:max "endRack" e:arg => hosts (ticket.donorKey (homeAt e)).1.2
local notation:max "endLow" e:arg => SiteDecode.localNumber (T).k slots (ctr e)

variable (age:i<S.length) (radix:S.radix=2^k)

variable (B:OrdinaryModel he prior.placement.stage choice (Fin (S.groupCount i)×prior.V))
local notation "world" => (B.named he T choice prior.order).result
local notation "act" => B.rawSite he T choice
variable (coh:n.result=(B.named he prior.placement.stage choice prior.order).result)
variable (places:∀x:(rawGraph he prior.placement.stage choice).Site,
  cast (congrArg (fun u:MarkedWorld F d P bits=>u.graph.Site) coh)
    (n.destination (rawInput he prior.placement.stage choice ((BitDescription.scannedRows he prior.placement.stage).state choice) x))=
    B.rawSite he prior.placement.stage choice x)
local notation "A₁" => modelStage (next:=next) B coh
local notation:max "raster₁" x:arg => ticket.parentVenue port.enough ((A₁).pos (act x)).2
local notation "key" => B.chart.key he T choice
local notation "last" => DescentSixParty.MarkedWorld.address (W.selected G (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice))
  key B.chart.hub (T).k gain
local notation:max "survives" e:arg => last (homeAt ((N).src (e).val))≠last (homeAt ((N).dst (e).val))
local notation:max "valueAt" e:arg => cell (sampleSlot e).1 (sampleSlot e).2
variable (pathWidth:breadth prior.placement.degree<2^fieldBits)
  (ticketWidth:(breadth prior.placement.degree+1)*DepotRAM.Material.roles
    (Stage.shapeOf (short:=short) prior.placement (donorNameBits prior.placement.stage.k prior.placement.stage.Δ))≤2^fieldBits)
local notation "full" => original_record_full (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch fieldBits age radix pathWidth ticketWidth

open DescentParallelBase DescentOrdinaryParentSupport DescentSharedCableNames DescentSixParty.MarkedWorld
local notation "pairNo" => PairRAM.globalNumberBy W.graph W.core home color (T).cap (originalId (ScanColonies he T))
local notation "oldCut" => B.old
local notation "chosenCut" => B.used
local notation "stageCut" => fun _ : (rr).pairs=>dvd_refl (T).z
local notation "ok" => model_bounds (next:=next) B coh
local notation "eqG" => model_grain ticket B coh
local notation "paths" => modelPaths (short:=short) (prior:=prior) (choice:=choice) win profile
local notation "routes" => model_paths (short:=short) (prior:=prior) (choice:=choice) win named fit winner df order profile B
local notation "groups'" => S.groupDigits age radix
local notation "placed" => fun x=> (model_sites ticket port age radix B coh places x).1
local notation "atV" => ticket.parentVenue port.enough
local notation "host" => DescentSharedCableNames.Stage.Host (Fin (S.groupCount (i+1))) next.V k
local notation "C₀" => DescentOrdinaryParentBlocks.blocks W G prior.order pairNo (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub (T).k gain (T).z oldCut chosenCut stageCut B.site A₁ (T).unitPos
variable (reciprocal:∀v u j,roster v j=some u→∃l,roster u l=some v)
attribute [local irreducible] originalRecord
local notation "Z₀" => originalMeasurement (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored
  dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal
local notation "markWorld" => (W.selected G (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice)).coalesced
  key B.chart.hub (T).k gain
local notation "newRole" => fun o:Fin (2^k*(A).cap*11)=>decide ((finProdFinEquiv.symm o : Fin (2^k*(A).cap) × Fin 11).2.val≠0)
local notation "lookup" => fun h:Fin H=>if has:∃v,hosts v=h then some has.choose else none
local notation "oldGroup" => fun a : Fin (S.groupCount (i+1)*2^k)=>(groups').symm (finProdFinEquiv.symm a)
local notation "panel" => DescentOrdinarySignedMeta.donorPanel W G A native S prior.valid rank (lookup) (oldGroup)
local notation "nextGroup" => Equiv.refl (Fin (S.groupCount (i+1)))

attribute [local irreducible] DescentOrdinaryMarkProject.bits

private theorem paidMarkAtOriginalHosts {newH:ℕ} (room:Fintype.card next.V≤newH)
    (x:Fin (2^k)) (j:Fin (breadth (A).degree*(2^k*(A).cap*11))) (v:Fin newH) (group:Fin (S.groupCount (i+1)))
    (u:host) (got:DescentDatedAddressBook.SignedExtent.wholeHost (nextGroup).toEmbedding
      (next.vertex.trans (Fin.castLEEmb room)) x v group=some u)
    (e:Local C₀ u) (selected:(Measured.roster C₀ roster reciprocal (Z₀)).address u e=j) :
    (DescentOrdinaryMarkProject.bits (Gather.select (Gather.reaching roster)) (panel) (newRole) (pitch) x j v group).val=1
      ↔ e.val∈(markWorld).core :=by
  have present (v : V) : (lookup) (hosts v)=some v :=by
    change (if h:∃a,hosts a=hosts v then some h.choose else none)=some v
    split
    next h => exact congrArg some ((hosts).injective h.choose_spec)
    next h => exact (h ⟨v,rfl⟩).elim
  have receipt := DescentOrdinaryParentSupport.paid_mark_at_hosts
    («I»:=(rr).pairs) («J₀»:=Fin (S.groupCount i)) («V₀»:=prior.V) («J»:=Fin (S.groupCount (i+1))) («V»:=next.V)
    («stage»:=k) («i»:=i+1) («a₀»:=i) («k₀»:=k) («hosts»:=H) («groups»:=S.groupCount i) («D»:=(A).degree)
    («Q»:=Q) («K»:=K₀) («L»:=next.placement.cap) («H₁»:=newH) («G₁»:=S.groupCount (i+1))
    W G prior.order pairNo (rr).pick
    (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub (T).k gain (T).z
    oldCut chosenCut stageCut B.site A₁ S ok eqG (T).unitPos A prior.valid rank groups' paths routes placed
    hosts grp roster atV (Z₀).read (Z₀).reached (Z₀).survives (Z₀).orientation (Z₀).shortTicket
    reciprocal (lookup) present (nextGroup) (next.vertex.trans (Fin.castLEEmb room)) (pitch)
    (fun u=>ticket.parentVenue_ordinal port.enough u.1.2) (fun u=>ticket.parentVenue_low port.enough u.1.2)
    x j v group u got e selected
  have identifyPanel := DescentOrdinarySignedMeta.donorPanel_relabel W G A native S prior.valid rank
    (lookup) (grp).symm (fun j₀ : Fin (S.groupCount (i+1)*2^k) =>
      (grp) ((groups').symm ((nextGroup).symm (finProdFinEquiv.symm j₀).1,(finProdFinEquiv.symm j₀).2)))
  exact Eq.mp (congrArg (fun p =>
    (DescentOrdinaryMarkProject.bits (Gather.select (Gather.reaching roster)) p (newRole) (pitch) x j v group).val = 1
      ↔ e.val ∈ (markWorld).core) identifyPanel) receipt

end

private abbrev OriginalMarkAtHosts : Prop := type_of% (@paidMarkAtOriginalHosts)

/-- On the canonical measured parent, the actual flag decoded from its old signed source
is precisely membership in the surviving coarse core. Ghosts never require a read. -/
theorem original_mark_known : OriginalMarkAtHosts := @paidMarkAtOriginalHosts

end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
