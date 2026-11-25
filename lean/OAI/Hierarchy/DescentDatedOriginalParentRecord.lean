import OAI.Hierarchy.DescentDatedOriginalParentPaths
import OAI.Hierarchy.DescentOrdinaryMaterialParentRecord
import OAI.Hierarchy.DescentOrdinaryIssuedTicket

namespace OAI
/-! # Retained ordinary parent mass and exact support in the original finite address raster -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
private theorem groupSeat_within {groups k cap : ℕ} (j : Fin ((groups*2^k*cap)*11)) :
    (DescentOrdinaryIssuedTicket.within j).val=((groupSeat j).2.1.val*cap+(groupSeat j).2.2.1.val)*11+
      (groupSeat j).2.2.2.val :=by
  obtain ⟨⟨q,role⟩,rfl⟩:=finProdFinEquiv.surjective j
  obtain ⟨⟨gx,t⟩,rfl⟩:=finProdFinEquiv.surjective q
  obtain ⟨⟨g,x⟩,rfl⟩:=finProdFinEquiv.surjective gx
  simp only [DescentOrdinaryIssuedTicket.within,groupSeat,Equiv.symm_apply_apply,finProdFinEquiv_apply_val]
  ring

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

def originalRecord (h : Fin H) (g : J) (z : DepotRAM.Material.Seat fmt) :=
  DepotRAM.Material.parent fmt form (measured h g) (rev h) z (roomAt h g z)

local notation:max "cell" h:arg j:arg => originalRecord ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch fieldBits h (groupSeat j).1 (groupSeat j).2
local notation:max "row" h:arg j:arg => (measured h (groupSeat j).1)
local notation:max "endLow" e:arg => SiteDecode.localNumber (T).k slots (ctr e)
local notation:max "endRack" e:arg => hosts (ticket.donorKey (homeAt e)).1.2
local notation:max "read" h:arg j:arg side:arg => DepotRAM.atSeat fmt profile G.b slots side (row h j)
                       (groupSeat j).2.1 (groupSeat j).2.2.1 (groupSeat j).2.2.2

theorem originalRecord_none (h : Fin H) (j : Fin (oldPorts*11)) (missing : units h j=0) :
    cell h j=none:=DepotRAM.Material.parent_missing fmt form _ _ _ _ missing

set_option maxHeartbeats 1400000 in
/-- The original source record determines both normalized endpoint coordinates, its complete mass,
and the comparison ticket made from the old outgoing ordinal and role at this source. -/
theorem original_record_live (pathWidth:P₀<2^fieldBits) (ticketWidth:K₀≤2^fieldBits)
    (e : positiveRows) (cross : owner ((N).src e.val)≠owner ((N).dst e.val)) (live : 0<(N).width e.val/(A).z) :
    let d:=sampleSlot e
    ∃record,cell d.1 d.2=some record ∧
      Gather.reaching roster d.1 (record).src.path=some (endRack ((N).src e.val)) ∧
      Gather.reaching roster d.1 (record).dst.path=some (endRack ((N).dst e.val)) ∧
      (record).src.low.val=endLow ((N).src e.val) ∧ (record).dst.low.val=endLow ((N).dst e.val) ∧
      (record).weight.val=(N).width e.val/(A).z ∧
      (record).ticket.val=Rebase.value roster .rank d.1 (record).src.path*DepotRAM.Material.roles fmt+
        (DescentOrdinaryIssuedTicket.within d.2).val ∧
      read d.1 d.2 false=Packed.token (some (record).src.path) ∧ read d.1 d.2 true=Packed.token (some (record).dst.path) :=by
  intro d
  have weight:=original_parent_mass ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth e
  simp only [ite_eq_right cross] at weight
  obtain ⟨p,both⟩:=original_parent_endpoints (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile dest issued roster mounted e cross
  have left:=both false
  have right:=both true
  let sl:=ActorPath.index (A).degree p.1
  let sr:=ActorPath.index (A).degree p.2
  have dl:=original_parent_low (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth false e cross
  have dr:=original_parent_low (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth true e cross
  have fitRoom : DepotRAM.Material.ParentRoom fmt form (row d.1 d.2)
      (rev d.1) (groupSeat d.2).2 Q K₀ next.placement.cap :=
    roomAt d.1 (groupSeat d.2).1 (groupSeat d.2).2
  have output := DepotRAM.Material.parent_emitted fmt form (row d.1 d.2)
    (groupSeat d.2).2 («H»:=H) («Q»:=Q) (K:=K₀) (L:=next.placement.cap)
    roster d.1 fitRoom sl sr left.1 right.1 (weight.trans_gt live).ne' pathWidth ticketWidth
  obtain ⟨record,issued_,r0,r1,rl,rr_,mass,_,serial⟩ := output
  have leftData : read d.1 d.2 false=Packed.token (some sl) ∧
      Gather.reaching roster d.1 sl=some (endRack ((N).src e.val)) := left
  have rightData : read d.1 d.2 true=Packed.token (some sr) ∧
      Gather.reaching roster d.1 sr=some (endRack ((N).dst e.val)) := right
  refine ⟨record,issued_,(congrArg (Gather.reaching roster d.1) r0).trans leftData.2,
    (congrArg (Gather.reaching roster d.1) r1).trans rightData.2,
    rl.trans dl,rr_.trans dr,mass.trans weight,?_,
    leftData.1.trans (congrArg (fun z : Fin P₀ => Packed.token (some z)) r0.symm),
    rightData.1.trans (congrArg (fun z : Fin P₀ => Packed.token (some z)) r1.symm)⟩
  exact serial.trans (congrArg₂ Nat.add
    (congrArg (fun z : Fin P₀ => Rebase.value roster .rank d.1 z * DepotRAM.Material.roles fmt) r0.symm)
    (groupSeat_within (groups:=S.groupCount i) (k:=k) (cap:=(A).cap) d.2).symm)


theorem originalRecord_absent (h : Fin H) (j : Fin (oldPorts*11))
    (vacant : ¬∃e:positiveRows,sampleSlot e=(h,j) ∧ owner ((N).src e.val)≠owner ((N).dst e.val) ∧
        0<(N).width e.val/(A).z) : cell h j=none :=by
  apply originalRecord_none
  by_contra positive
  exact vacant ((original_parent_nonzero ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth h j).1 positive)

theorem originalRecord_padded (h : Fin H) (j : Fin (oldPorts*11)) (past : Fintype.card V≤h.val) :
    cell h j=none :=by
  apply originalRecord_absent
  rintro ⟨e,placed,_,_⟩
  have hostValue:=congrArg (fun z:Fin H×Fin (oldPorts*11)=>z.1.val) placed
  change (prior.vertex ((A).pos (W.graph.src (anchor (rr).pick e.val))).2).val=h.val at hostValue
  exact Nat.not_lt_of_ge past (hostValue ▸ (prior.vertex ((A).pos (W.graph.src (anchor (rr).pick e.val))).2).isLt)

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
