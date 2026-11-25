import OAI.Hierarchy.DescentDatedRawCaptureFields
import OAI.Hierarchy.DescentOrdinaryMaterialParentRoom
import OAI.Hierarchy.DescentOrdinaryMaterialPitch

namespace OAI
/-! # Retained ordinary parent mass and exact support in the original finite address raster -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
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
local notation "r" => 2^k
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

include ticket named fit winner df order sumSize stored mounted birth in
theorem original_parent_report (h : Fin H) (j : Fin (oldPorts*11)) :
    units h j=liveMass (ticket.issuedPanel hosts h j) :=by
  let pair:=finProdFinEquiv.symm j
  let seat:=finProdFinEquiv.symm pair.1
  let gx:=finProdFinEquiv.symm seat.1
  have local_:=raw_seat_donor ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth h gx.1 gx.2 seat.2
  have id : finProdFinEquiv (finProdFinEquiv (gx.1,gx.2),seat.2)=pair.1 :=
    (congrArg (fun z => finProdFinEquiv (z,seat.2))
      (finProdFinEquiv.apply_symm_apply seat.1)).trans (finProdFinEquiv.apply_symm_apply pair.1)
  have donor := local_.trans (congrArg (ticket.measuredDonors hosts h) id)
  have source:=ticket.donor_words hosts h j
  change report (T).k gain slots (ticket.measuredDonors hosts h pair.1) pair.2=_ at source
  change liveMass (report (T).k gain slots (DepotRAM.seatDonor fmt profile G.b slots (measured h gx.1)
    gx.2 seat.2) pair.2)=_
  exact congrArg liveMass ((congrArg (fun d₀ => report (T).k gain slots d₀ pair.2) donor).trans source)

include ticket named fit winner df order sumSize stored mounted birth in
theorem original_parent_mass (e : positiveRows) :
    units (sampleSlot e).1 (sampleSlot e).2 =
      if owner ((N).src e.val)=owner ((N).dst e.val) then 0 else (N).width e.val/(A).z :=by
  exact (original_parent_report ticket port win hm named fit winner df order profile b m sumSize stored dest issued
    roster mounted birth _ _).trans (ticket.signed_units hosts e)

include ticket named fit winner df order sumSize stored mounted birth in
theorem original_parent_nonzero (h : Fin H) (j : Fin (oldPorts*11)) :
    units h j≠0 ↔ ∃e:positiveRows,sampleSlot e=(h,j) ∧ owner ((N).src e.val)≠owner ((N).dst e.val) ∧ 0<(N).width e.val/(A).z :=by
  rw [original_parent_report ticket port win hm named fit winner df order profile b m sumSize stored dest issued
    roster mounted birth h j]
  constructor
  · intro active
    by_cases found:∃e:positiveRows,sampleSlot e=(h,j)
    · obtain ⟨e,at_⟩:=found
      have hit:=ticket.signed_units hosts e
      rw [at_] at hit
      change liveMass (ticket.issuedPanel hosts h j)=_ at hit
      rw [hit] at active
      split at active
      next _=>exact (active rfl).elim
      next dif=>exact ⟨e,at_,dif,Nat.pos_of_ne_zero active⟩
    · exact (active (ticket.signed_units_hole hosts h j found)).elim
  · rintro ⟨e,at_,dif,live⟩
    have hit:=ticket.signed_units hosts e
    rw [at_,ite_eq_right dif] at hit
    exact hit.trans_gt live |>.ne'

local notation "homeAt" => newSite W.graph (rr).pick lay (rr).pack
local notation:max "ctr" e:arg => mergeHub ticket.donorHub (T).k gain (ticket.donorKey (homeAt e))
local notation:max "lowAt" h:arg j:arg b:arg => (roleLow (T).k gain slots b
  (DepotRAM.seatDonor fmt profile G.b slots (measured h (groupSeat j).1) (groupSeat j).2.1 (groupSeat j).2.2.1)
  (groupSeat j).2.2.2).val

set_option maxHeartbeats 700000 in
include ticket named fit winner df order sumSize stored mounted birth in
theorem original_parent_low (side : Bool) (e : positiveRows)
    (kept : owner ((N).src e.val)≠owner ((N).dst e.val)) :
    lowAt (sampleSlot e).1 (sampleSlot e).2 side=
      SiteDecode.localNumber (T).k slots (ctr (if side then (N).dst e.val else (N).src e.val)) :=by
  let anchor₀:DescentSharedCableNames.Stage.Positive A:=⟨DescentCableDonorNames.anchor (rr).pick e.val,e.property⟩
  let t:=oldSlot A S prior.valid native hosts grp anchor₀
  let cut:=finProdFinEquiv.symm t.2
  let gx:=finProdFinEquiv.symm cut.1
  have sample : sampleSlot e=(t.1,finProdFinEquiv (t.2,DescentCableDonorNames.role e.val)):=rfl
  have attached:=raw_seat_donor ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth t.1 gx.1 gx.2 cut.2
  have loc:finProdFinEquiv (finProdFinEquiv (gx.1,gx.2),cut.2)=t.2 :=
    (congrArg (fun z => finProdFinEquiv (z,cut.2))
      (finProdFinEquiv.apply_symm_apply cut.1)).trans (finProdFinEquiv.apply_symm_apply t.2)
  rw [loc] at attached
  have row:=occupied_read (a:=bytes) (hCode:=(T).k) A S prior.valid native hosts grp (rr).pick lay (rr).pack
    ticket.donorKey ticket.donorHub slots ((rr).profile choice) (relative (rr).pick lay (rr).pack ticket.donorKey) anchor₀
  refine (congrArg (fun z₀ : Fin H × Fin (oldPorts*11) => lowAt z₀.1 z₀.2 side) sample).trans ?_
  simp only [groupSeat,Equiv.symm_apply_apply]
  change (roleLow (T).k gain slots side (DepotRAM.seatDonor fmt profile G.b slots
    (measured t.1 gx.1) gx.2 cut.2) (DescentCableDonorNames.role e.val)).val=_
  rw [attached]
  unfold OrdinaryLink.measuredDonors
  change (roleLow (T).k gain slots side (physicalRows (a:=bytes) (hCode:=(T).k) A S prior.valid native hosts grp (rr).pick lay
    (rr).pack ticket.donorKey ticket.donorHub slots ((rr).profile choice)
    (relative (rr).pick lay (rr).pack ticket.donorKey) t.1 t.2) (DescentCableDonorNames.role e.val)).val=_
  rw [row]
  have frame:=(IssuedRows.common_chart he T choice ticket.issued ((rr).state choice)).choose_spec.1
  have surviving : ctr ((N).src e.val) ≠ ctr ((N).dst e.val) :=by
    intro eqn
    unfold OrdinaryLink.donorKey at eqn
    exact kept (congrArg (originalId _) ((frame.2 _ _).mpr eqn))
  apply survivor_label («A»:=A) (S:=S) (ready:=prior.valid) (pick:=(rr).pick) (layout:=lay)
    (pack:=(rr).pack) (key:=ticket.donorKey) (hub:=ticket.donorHub) (profile:=(rr).profile choice)
    (valid:=by unfold OrdinaryLink.donorKey; exact frame.1) (ids:=Nat.le_pow_clog (by decide:1<2) _) (side:=side) (e:=e) (survives:=surviving)

include ticket named fit winner df order sumSize stored mounted birth in
theorem original_low_range (side : Bool) (h : Fin H) (j : Fin (oldPorts*11)) (positive : units h j≠0) :
    lowAt h j side < (2^((T).k+1)-1)*slots :=by
  obtain ⟨e,address,diff,_⟩:=(original_parent_nonzero ticket port win hm named fit winner df order profile
    b m sumSize stored dest issued roster mounted birth h j).1 positive
  have decode:=original_parent_low ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth side e diff
  have move := congrArg (fun z₀ : Fin H × Fin (oldPorts*11) => lowAt z₀.1 z₀.2 side) address.symm
  have legal : ∀v, ticket.donorKey v ∈ keys (T).k slots := by
    unfold OrdinaryLink.donorKey
    exact (IssuedRows.common_chart he T choice ticket.issued ((rr).state choice)).choose_spec.1.1
  exact (move.trans decode).trans_lt (SiteDecode.local_number_pitch (DescentHostDirectory.merged_mem_keys
    ticket.donorHub (T).k gain slots (legal _)))

include ticket in
theorem target_units (e : positiveRows) : (N).width e.val/(A).z≤next.placement.cap :=by
  have width (t : (rr).pairs×Fin 2) : W.graph.width ((rr).pick t)=(A).z*G.b :=
    ((rr).fit t.1 t.2).trans (congrArg (·*G.b) ticket.quantum)
  have equal:=normalized_width A S prior.valid (rr).pick ((rr).profile choice) width e.val
  have real : (GadgetNetwork.physical W.graph (rr).pick (branchWidth G (fun _=>(A).z) ((rr).profile choice))).width e.val=(N).width e.val :=by
    rcases e.val with f|⟨j,b⟩|⟨j,b⟩
    · rfl
    · rfl
    · change (A).z*_=(T).z*_;rw [ticket.quantum]
  rw [←real,←equal,Nat.mul_div_cancel _ (A).unitPos,ticket.capacity]
  apply (normalized_bound A S prior.valid ((rr).profile choice) e.val).trans
  have gain₄ : 4≤2^(gainExponent 20 D):=Nat.pow_le_pow_right (by decide:0<2) (show 2≤gainExponent 20 D by
    unfold gainExponent;omega)
  have upper : 4*G.b≤2^(gainExponent 20 D)*G.b*(A).cap:=
    (Nat.mul_le_mul_right _ gain₄).trans (Nat.le_mul_of_pos_right _ (A).capPos)
  apply max_le
  · rw [Nat.mul_comm (A).cap G.b]
    rw [Nat.mul_assoc]
    exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  · exact (show G.C+1+G.k≤4*G.b by have:=G.paid;omega).trans upper

set_option maxHeartbeats 900000 in
include ticket named fit winner df order sumSize stored mounted birth in
theorem original_mass_bound (h : Fin H) (j : Fin (oldPorts*11)) :
    units h j≤next.placement.cap :=by
  by_cases blank : units h j=0
  · simp [blank]
  obtain ⟨e,where_,diff,_⟩:=(original_parent_nonzero ticket port win hm named fit winner df order profile
    b m sumSize stored dest issued roster mounted birth h j).1 blank
  have exactMass:=original_parent_mass ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth e
  rw [where_,ite_eq_right diff] at exactMass
  exact le_trans (le_of_eq exactMass) (target_units ticket e)

set_option maxHeartbeats 900000 in
include ticket named fit winner df order sumSize stored mounted birth in
/-- A bounds proof for every old mixed-radix cell, including padded hosts and ghost role addresses. -/
theorem original_parent_room (pitch fieldBits : ℕ) (R : Fin H→Fin (A).degree→Option (Fin H))
    (h : Fin H) (g : J) (z₀ : DepotRAM.Material.Seat fmt) :
    let f:=rawFormat (G:=G) (prior:=prior) profile pitch fieldBits
    DepotRAM.Material.ParentRoom fmt f (measured h g)
      (DescentHaloPackedRebase.digest (DepotRAM.Material.reverseEntries fmt R h)) z₀
      (2^((T).k+1)*slots) ((breadth (A).degree+1)*DepotRAM.Material.roles fmt) next.placement.cap :=by
  intro f
  let j:Fin (oldPorts*11):=finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (g,z₀.1),z₀.2.1),z₀.2.2)
  have unwrap : groupSeat j=(g,z₀):=by
    rcases z₀ with ⟨x,t,role⟩
    simp only [groupSeat,j,Equiv.symm_apply_apply]
    rfl
  apply DepotRAM.Material.parent_room fmt f (measured h g) z₀ R h le_rfl
  · intro t exists_
    have existsMass:=DepotRAM.Material.active_mass fmt f (measured h g) z₀ exists_
    have positive : units h j≠0:=by
      rw [unwrap]
      exact existsMass
    have bounds:=original_low_range ticket port win hm named fit winner df order profile b m sumSize stored
      dest issued roster mounted birth (decide (t.val=1)) h j positive
    rw [unwrap] at bounds
    exact bounds.trans_le (Nat.mul_le_mul_right _ (Nat.sub_le ..))
  · intro _
    have bounds:=original_mass_bound ticket port win hm named fit winner df order profile b m sumSize stored
      dest issued roster mounted birth h j
    rw [unwrap] at bounds
    exact bounds

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
