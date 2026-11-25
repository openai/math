import OAI.Hierarchy.DescentDatedOriginalParentRecord
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
set_option quotPrecheck false
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
variable (pitch fieldBits : ℕ)
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

include age radix in
private theorem parent_at_venue (x:(N).Site) :
    (venue x).1=endRack x ∧ (venue x).2.val=endLow x :=by
  have read:=ticket.parentVenue_raw_location port.enough age radix x
  dsimp only at read
  rw [ticket.rawParentKey_donor x] at read
  constructor
  · refine read.2.1.trans ?_
    unfold mergeHub
    split <;>rfl
  · exact read.2.2

variable (pathWidth : breadth prior.placement.degree < 2^fieldBits)
    (ticketWidth : (breadth prior.placement.degree+1) *
      DepotRAM.Material.roles (Stage.shapeOf (short:=short) prior.placement
        (donorNameBits prior.placement.stage.k prior.placement.stage.Δ)) ≤ 2^fieldBits)
local notation "get" => original_record_live (short:=short) (a:=a) (w:=w) ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch fieldBits pathWidth ticketWidth

include age radix pathWidth ticketWidth in
theorem original_record_source (e:positiveRows) (cross:owner ((N).src e.val)≠owner ((N).dst e.val))
    (paid:0<(N).width e.val/(A).z) :
    let d:=sampleSlot e
    ∃s, cell d.1 d.2=some s ∧ Witness roster d.1 s (venue ((N).src e.val)) (venue ((N).dst e.val)) ∧
      s.weight.val=(N).width e.val/(A).z ∧ s.ticket.val=Rebase.value roster .rank d.1 s.src.path*DepotRAM.Material.roles fmt+
        (DescentOrdinaryIssuedTicket.within d.2).val :=by
  obtain ⟨s,read,left,right,lowA,lowB,mass,ticket₀,_⟩:=get e cross paid
  have a:=parent_at_venue ticket port age radix ((N).src e.val)
  have b:=parent_at_venue ticket port age radix ((N).dst e.val)
  exact ⟨s,read,⟨left.trans (congrArg some a.1.symm),right.trans (congrArg some b.1.symm),
    Fin.ext (lowA.trans a.2.symm),Fin.ext (lowB.trans b.2.symm)⟩,mass,ticket₀⟩

include age radix pathWidth ticketWidth in
/-- Numeric comparison on any two earlier positive records at a common actual post-trim source. -/
theorem original_record_order (reciprocal:∀v u j,roster v j=some u→∃l,roster u l=some v)
    (e f:positiveRows) (keep : ∀t∈([e,f]:List _),owner ((N).src t.val)≠owner ((N).dst t.val) ∧ 0<(N).width t.val/(A).z)
    (common:owner ((N).src e.val)=owner ((N).src f.val))
    {a b'} (ea:cell (sampleSlot e).1 (sampleSlot e).2=some a)
    (fb:cell (sampleSlot f).1 (sampleSlot f).2=some b') :
    a.ticket<b'.ticket ↔ (sampleSlot e).1<(sampleSlot f).1 ∨
      (sampleSlot e).1=(sampleSlot f).1 ∧
      DescentOrdinaryIssuedTicket.within (sampleSlot e).2<DescentOrdinaryIssuedTicket.within (sampleSlot f).2 :=by
  have E:=keep e (by simp)
  have F':=keep f (by simp)
  obtain ⟨sa,saEq,wa,_,ta⟩:=original_record_source ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch fieldBits age radix pathWidth ticketWidth e E.1 E.2
  obtain ⟨sb,sbEq,wb,_,tb⟩:=original_record_source ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch fieldBits age radix pathWidth ticketWidth f F'.1 F'.2
  have aa:=Option.some.inj (saEq.symm.trans ea)
  have bb:=Option.some.inj (sbEq.symm.trans fb)
  rw [←aa,←bb]
  have same : current ((N).src e.val) = current ((N).src f.val):= (originalId n.result.graph.Site).injective common
  have A0:=wa.src
  have B0:=wb.src
  rw [same] at A0
  change sa.ticket.val<sb.ticket.val ↔ _
  rw [ta,tb]
  let O:=DepotRAM.Material.roles fmt
  let l : Fin O:=⟨(DescentOrdinaryIssuedTicket.within (sampleSlot e).2).val,by
    change _ < 2^k*((A).cap*11)
    simpa only [Nat.mul_assoc] using (DescentOrdinaryIssuedTicket.within (sampleSlot e).2).isLt⟩
  let r' : Fin O:=⟨(DescentOrdinaryIssuedTicket.within (sampleSlot f).2).val,by
    change _ < 2^k*((A).cap*11)
    simpa only [Nat.mul_assoc] using (DescentOrdinaryIssuedTicket.within (sampleSlot f).2).isLt⟩
  exact DescentOrdinaryIssuedTicket.anchor_order roster reciprocal _ _ _ _ _ A0 B0 l r'
include age radix pathWidth ticketWidth in
/-- A present old record is paid by a genuine raw parent and has exactly that parent's endpoint witness.
This also excludes dormant old/arm/supply roles at honest partially filled donor addresses. -/
theorem original_record_full (h:Fin H) (j:Fin (oldPorts*11)) {s} (hit:cell h j=some s) :
    ∃e:positiveRows,sampleSlot e=(h,j) ∧ owner ((N).src e.val)≠owner ((N).dst e.val) ∧
      0<(N).width e.val/(A).z ∧ Witness roster h s (venue ((N).src e.val)) (venue ((N).dst e.val)) ∧
      s.weight.val=(N).width e.val/(A).z :=by
  have live:units h j≠0:=by
    intro zero
    have none:=originalRecord_none ticket port win hm named fit winner df order profile b m sumSize stored
      dest issued roster mounted birth pitch fieldBits h j zero
    rw [none] at hit
    contradiction
  obtain ⟨e,site,kept,paid⟩:=(original_parent_nonzero ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth h j).1 live
  obtain ⟨t,read,ends,mass,_⟩:=original_record_source ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch fieldBits age radix pathWidth ticketWidth e kept paid
  rw [site] at read ends
  have eq:=Option.some.inj (read.symm.trans hit)
  exact ⟨e,site,kept,paid,eq ▸ ends,eq ▸ mass⟩

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
