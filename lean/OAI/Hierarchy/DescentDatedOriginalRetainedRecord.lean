import OAI.Hierarchy.DescentDatedOriginalParentStage
import OAI.Hierarchy.DescentDatedOriginalParentUpper
import OAI.Hierarchy.DescentOrdinaryParentTicketOrder
import OAI.Hierarchy.DescentOrdinaryParentVenue
import OAI.Hierarchy.DescentOrdinaryParentTicketCompare

namespace OAI
/-! The original emitted tuple reaches the two actual normalized venues. -/
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
local notation "full" => original_record_full (short:=short) (w:=w) (a:=a) (prior:=prior) ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch fieldBits age radix pathWidth ticketWidth

include places in
theorem model_different (x y:(N).Site) :
    last (homeAt x)≠last (homeAt y) ↔ owner x≠owner y :=by
  let types := congrArg (fun u : MarkedWorld F d P bits => u.graph.Site) coh
  have actual : current x = current y ↔ act x = act y :=
    ⟨fun h => (places x).symm.trans ((congrArg (cast types) h).trans (places y)),
     fun h => (cast_inj types).mp ((places x).trans (h.trans (places y).symm))⟩
  have sites : last (homeAt x) = last (homeAt y) ↔ act x = act y :=
    (B.siteMap he T choice).injective.eq_iff.symm
  have ownerEq : owner x = owner y ↔ current x = current y :=
    (originalId n.result.graph.Site).injective.eq_iff
  exact not_congr ((sites.trans actual.symm).trans ownerEq.symm)


include places pathWidth ticketWidth in
theorem model_original_present (e:positiveRows) (kept:survives e) (paid:0<(N).width e.val/(T).z) :
    ∃r,valueAt e=some r:=by
  have keep:owner ((N).src (e).val)≠owner ((N).dst (e).val):=(model_different B coh places _ _).1 kept
  exact (original_record_live ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch fieldBits pathWidth ticketWidth e keep paid).imp (fun _ p=>p.1)

attribute [local irreducible] originalRecord

set_option maxHeartbeats 1200000 in
include places age radix pathWidth ticketWidth in
theorem model_original_fields (e:positiveRows) {r} (seen:valueAt e=some r) :
    survives e ∧ 0<(N).width e.val/(T).z ∧
      r.weight.val=(N).width e.val/(T).z ∧
      Witness roster (sampleSlot e).1 r (raster₁ ((N).src (e).val)) (raster₁ ((N).dst (e).val)) ∧
      r.upper=DescentParallelBase.side B.site (last (homeAt ((N).src (e).val))) (last (homeAt ((N).dst (e).val))) :=by
  have record := full (sampleSlot e).1 (sampleSlot e).2 (s:=r) seen
  obtain ⟨f,back,cross,paid,endRead,mass⟩ := record
  have eqn : f=e:=(sampleSlot).injective back
  subst f
  have here:=model_placement (next:=next) B coh places ((N).src (e).val)
  have there:=model_placement (next:=next) B coh places ((N).dst (e).val)
  refine ⟨(model_different B coh places _ _).2 cross,paid,mass,?_,?_⟩
  · rw [here.1,there.1]
    exact endRead
  · have dir:=original_record_upper ticket port win hm named fit winner df order profile b m sumSize stored
      dest issued roster mounted birth fieldBits pathWidth ticketWidth e cross paid r seen
    refine dir.trans (decide_eq_decide.mpr ?_)
    exact B.old_rank he T choice prior.order ((rr).state choice) coh places ((N).dst (e).val) ((N).src (e).val)

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
