import OAI.Hierarchy.DescentReachedRetainedHub
import OAI.Hierarchy.DescentPhysicalBeforeRankPorts
import OAI.Hierarchy.DescentPhysicalSheetEntryFrame
import OAI.Hierarchy.DescentDatedRetainedSpace
import OAI.Hierarchy.DescentDatedPacketSnapshot
import OAI.Hierarchy.DescentPhysicalPreviousFieldFrame
import OAI.Hierarchy.DescentOperandSourcesBeforePacket
import OAI.Hierarchy.DescentResetConvertedOld

namespace OAI
/-! # Reading the source sibling ticket across the original operand setup -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentResetTrunkCompactPointer DescentDyadicSpan DescentSIMDLookup DescentPackedZip DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "A" => (v).receiver
local notation "C" => (v).setup
local notation "p" => (v).linkedRankInputs u.sectors ((v).sheetsStart b)
local notation "book" => (v).rankBook p b
local notation "r" => (v).renderFromRanks p b
local notation:max "rk" ok:arg m:arg => (book).memory (((v).rankPortPhase b w).image (u.candidateEntry ok m))
local notation "first" => (v).operandFloor b
local notation:max "last" ok:arg m:arg => ((C).code first w u.bank u.laws).image (u.beforeSetupImage ok m)

private theorem retained_order (ok : u.Ready) :
    (v).rankEnd b≤(v).controlFloor b ∧ (v).controlFloor b≤first ∧
    first≤(C).placed first ∧ (C).placed first≤(C).endAddress first ∧ (C).endAddress first<2^w :=by
  have gate:=((A).occupied ((v).fieldsEnd b)).1
  have dates:=(v).control_address_bounds b
  obtain ⟨ca,cb,cc,cd,ce,cf,cg,ch⟩:=(C).order first
  have entry : first≤(C).placed first:=by rw [(C).placed_shift];omega
  have placed : (C).placed first≤(C).packetEnd first:=((C).packets.join _).1.trans ((C).packets.join _).2
  have cast : (C).packetEnd first≤(C).publicEnd first:=Nat.le_add_right ..
  have ceiling := (v).keep_before b
  have runs:=(v).operand_order b
  exact ⟨(Nat.le_add_right ..).trans gate,dates.2.2.1,entry,by omega,
    (ceiling.trans (runs.1.trans (runs.2.trans ((v).final_ge b)))).trans_lt ok.full⟩

/-- The renderer and control-register compiler both preserve the earned rank
bank and every earlier word used to locate its compact source sibling. -/
theorem retained_rank_frame (ok : u.Ready) (m : Memory w) :
    PrefixAgreement.Low ((v).rankEnd b) (u.beforeSetupImage ok m) (rk ok m) :=by
  let ranked:=rk ok m
  have bounds:=(v).control_address_bounds b
  have cut:=u.retained_order ok
  have endRoom:=bounds.2.2.2.trans_lt ok.full
  have rankRoom:=(cut.1.trans bounds.2.2.1).trans_lt endRoom
  have before : ∀x j,((p).header x j).Fits w ((v).rankEnd b) := by
    intro x j
    obtain ⟨h,i,k,o⟩:=(book).ordered
    exact ProtocolRAMGeneratedWrite.fits_mono _ (((h.trans i).trans k).trans o) (ok.ranks.header x j)
  have printed:=(v).render_any r b u.degree ranked ok.width before
    ((book).finalRank_fits ok.ranks rankRoom) (bounds.2.2.1.trans_lt endRoom)
  have ctl:=(v).controlRegisters.any ((v).controlFloor b) ((v).actor.scene ((v).middle.stop b))
    u.bank.count u.bank.inverse ((v).renderMemory r b u.degree ranked) ok.controls endRoom
  intro z hz
  exact (ctl.2 z (.inl (hz.trans_le cut.1))).trans (printed.2.1 z (.inl hz))

/-- A scalar or packed control read through the original rank bank remains
valid after every native operand table has been mounted. -/
theorem from_rank_source (ok : u.Ready) (m : Memory w) {H G n M : ℕ} (e : Expr)
    (value : Fin H→Fin G→Cell n) (fits : e.Fits w ((v).rankEnd b))
    (read : Source e value M (rk ok m)) :
    Source e value M (last ok m) :=by
  have cut:=u.retained_order ok
  have setup:=(C).any first (u.beforeSetupImage ok m) u.bank u.laws ok.placed cut.2.2.2.2
  have low : PrefixAgreement.Low ((v).rankEnd b) (last ok m) (rk ok m):=fun i hi=>
    (setup.frame i (.inl (hi.trans_le (cut.1.trans cut.2.1)))).trans (u.retained_rank_frame ok m i hi)
  intro i
  exact (PrefixAgreement.expr e _ _ _ (PrefixAgreement.inputEnd_of_fits e fits) low _).trans (read i)

/-- The width conversion executes on the previous source-sibling ticket.
Its table and original side lookup both survive in the final operand state. -/
theorem dated_ticket_at (ok : u.Ready) (m : Memory w) (x : Fin (C).placement.blocks) (d : Fin (C).strip)
    (blocks : (C).placement.blocks=(A).blocks) (slot : (v).front.signedQueries/2+d.val<(A).candidates)
    {H G : ℕ} (value : Fin H→Fin G→Cell (C).ticketBits)
    (fromSibling : Source ((v).incomingTicketRow b x.val d.val) value (C).lanes (rk ok m)) :
    ((v).retainedTicket b x d).Fits w ((C).casts first) ∧
    Source ((v).retainedTicket b x d) (fun h g=>((value h g).val:Cell (C).fieldBits)) (C).lanes (last ok m) :=by
  have cut:=u.retained_order ok
  have roof:=cut.2.2.2.2
  have stop : (C).casts first≤(C).endAddress first:=by
    obtain ⟨ca,cb,cc,cd,ce,cf,cg,ch⟩:=(C).order first;omega
  have rr:=(cut.1.trans (cut.2.1.trans (cut.2.2.1.trans cut.2.2.2.1))).trans_lt roof
  have rankFit:=ProtocolRAMGeneratedWrite.fits_mono _ ((v).earlier b).2.1
    ((v).incoming_row_fits b x d blocks slot (((v).earlier b).2.1.trans_lt rr))
  have early:=(C).sources_run first (u.beforeSetupImage ok m) u.bank ok.placed (cut.2.2.2.1.trans_lt roof)
  let i:=(v).ticketColumn d
  let e:=(v).incomingTicketRow b x.val d.val
  let R (h : Fin H) (g : Fin G) : Cell ((C).width i):=Fin.cast (congrArg (fun z=>2^z) ((v).ticket_width d).symm) (value h g)
  have stored : Source e R (C).lanes (rk ok m):=by
    have casted {n t : ℕ} (same : n=t) (f : Fin H→Fin G→Cell n) (read : Source e f (C).lanes (rk ok m)) :
        Source e (fun h g=>Fin.cast (congrArg (fun z=>2^z) same) (f h g)) (C).lanes (rk ok m):=by
      subst t; exact read
    exact casted ((v).ticket_width d).symm value fromSibling
  have low : PrefixAgreement.Low ((v).rankEnd b) (((C).sources first w u.bank).image (u.beforeSetupImage ok m)) (rk ok m) :=
    fun j hj=>(early.frame j (.inl (hj.trans_le (cut.1.trans cut.2.1)))).trans (u.retained_rank_frame ok m j hj)
  have prior : Source e R (C).lanes (((C).sources first w u.bank).image (u.beforeSetupImage ok m)):=fun row_=>
    (PrefixAgreement.expr e _ _ _ (PrefixAgreement.inputEnd_of_fits e rankFit) low _).trans (stored row_)
  exact ⟨(v).retained_ticket_fits b x d blocks slot (stop.trans_lt roof),
    (C).converted_moved first u.bank u.laws (u.beforeSetupImage ok m) roof ok.placed i e R
      (ProtocolRAMGeneratedWrite.fits_mono _ (cut.1.trans (cut.2.1.trans cut.2.2.1)) rankFit) prior⟩

local notation "F₀" => (v).front
local notation "cut₀" => (v).actorEnd b
local notation "scene₀" => (v).issuedScene b u.earlier
local notation:max "trunk₀" m:arg => ((F₀).trunkScene cut₀ scene₀ u.sceneFits).image m

/-- Original compact trunk pointers are still present when the whole native
chronology scanner has finished, including unused rows. -/
theorem ranked_trunk_frame (ok : u.Ready) (m : Memory w) :
    PrefixAgreement.Low ((v).trunkEnd b) (rk ok m) (trunk₀ m) :=by
  have fromTrunk : (v).trunkEnd b≤(v).massEnd b:=by unfold ResetOutput.massEnd;rw [(v).contactShape.translate];omega
  have toPair:=((v).ranked_space_earlier b).2.1
  have toPort:=(v).rankPort_after b
  have cut:=u.retained_order ok
  have rr:=(cut.1.trans (cut.2.1.trans (cut.2.2.1.trans cut.2.2.2.1))).trans_lt cut.2.2.2.2
  have prt:=(v).rankPort_any b w (u.candidateEntry ok m) ok.rankPorts
  have ranked:=(book).any (((v).rankPortPhase b w).image (u.candidateEntry ok m)) ok.ranks rr
  have contact:=(v).contactShape.actual ((F₀).donorStart cut₀) ((v).trunkEnd b) (scene₀).donor
    u.sceneFits.donor ok.donors ok.mass ok.projectionLanes ok.projectionBlocks (trunk₀ m)
  intro z hz
  have h:=hz.trans_le fromTrunk
  exact (ranked.2.1 z (.inl ((h.trans_le toPair).trans_le toPort))).trans
    ((prt.2 z (.inl (h.trans_le toPair))).trans ((u.before_ports_frame ok m z h).trans (contact.2.2 z (.inl hz))))

/-- Original incoming chronology is read at the physically measured sibling.
Every memory transition from the compact pointer to the final operand input
is the one executed by the fixed date. -/
theorem dated_ticket_rows (ok : u.Ready) (m : Memory w) (x : Fin (C).placement.blocks) (d : Fin (C).strip)
    (blocks : (C).placement.blocks=(A).blocks) (slot : (F₀).signedQueries/2+d.val<(A).candidates)
    (hosts : (F₀).newHosts=(A).hosts) (groups : (F₀).peer.groups=(A).groups)
    (lanes : (F₀).peer.lanes=(A).lanes) (pitch : (C).lanes=(F₀).peer.lanes)
    {N P : ℕ} (rosterSize : P=(F₀).peer.hosts) (name : Fin N→Fin P) (other : Fin N→Option (Fin N))
    (live : N≤(F₀).newHosts) (active : N≤(scene₀).inverse.size)
    (census : Measured ((F₀).trunkBanks cut₀ scene₀) name other (((F₀).received cut₀ scene₀ u.sceneFits).image m))
    (value : Fin (F₀).newHosts→Fin (F₀).peer.groups→Cell (C).ticketBits)
    (ranked : Reads ((v).incomingTicketBank b x.val d.val) value (F₀).peer.lanes (rk ok m)) :
    ((v).retainedTicket b x d).Fits w ((C).casts first) ∧
    Source ((v).retainedTicket b x d) (fun h g=>(((pointer live other h).elim 0 (fun t=>value t g)).val:Cell (C).fieldBits))
      (C).lanes (last ok m) :=by
  have cut:=u.retained_order ok
  have step:=(v).correction_cuts b
  have tr:=(v).earlier b
  have rr:=(cut.1.trans (cut.2.1.trans (cut.2.2.1.trans cut.2.2.2.1))).trans_lt cut.2.2.2.2
  let end_ := (v).ticketEnd b
  have room : end_<2^w:=tr.2.1.trans_lt rr
  have bank:=DescentResetSourceTicketBank.column_fits («b»:=(v).ticketBits) (M:=(A).lanes)
    (H:=(A).hosts) (G:=(A).groups) (root:=(v).pairEnd b) (X:=(A).blocks) (K:=(A).candidates)
    room (x.cast blocks) ⟨(F₀).signedQueries/2+d.val,slot⟩
  let n₀ := (F₀).newHosts*chunks (F₀).peer.groups (F₀).peer.lanes
  let addr := DescentResetTrunkCompactGather.rows ((F₀).mixed cut₀) (F₀).newHosts (F₀).peer.groups (F₀).peer.lanes
  have width : n₀≤((v).incomingTicketBank b x.val d.val).size:=by
    change (F₀).newHosts*chunks (F₀).peer.groups (F₀).peer.lanes≤2^Nat.clog 2 ((A).hosts*chunks (A).groups (A).lanes)
    rw [hosts,groups,lanes];exact Nat.le_pow_clog (by decide) _
  have up : addr+span n₀=(F₀).gathered cut₀:=rfl
  have run : (F₀).gathered cut₀≤(v).trunkEnd b:=Nat.le_add_right ..
  have h:=(F₀).trunk_sibling_read cut₀ scene₀ u.sceneFits m (rk ok m) rosterSize name other live active census
    ok.trunk end_ room (run.trans step.1) ((v).incomingTicketBank b x.val d.val) value bank width ranked (by
      intro row_
      have hr : (row _ _ _ row_).val<n₀:= (row _ _ _ row_).isLt
      exact u.ranked_trunk_frame ok m _ ((Nat.add_lt_add_left (hr.trans_le (span_ge _)) addr).trans_le (up.le.trans run)))
  have gathered : Source ((v).incomingTicketRow b x.val d.val)
      (fun host g => (pointer live other host).elim 0 (fun t => value t g))
      (F₀).peer.lanes (rk ok m) := h.2
  exact u.dated_ticket_at ok m x d blocks slot _ (by simpa only [pitch] using gathered)

/-- The marked bit is evaluated on the actual received trunk-header shelf
before ranking. Subsequent phases leave all its input words readable. -/
theorem dated_marked_at (ok : u.Ready) (m : Memory w) (x : Fin (C).placement.blocks)
    {H G : ℕ} (value : Fin H→Fin G→Cell (C).fieldBits)
    (prior : ((v).retainedHub b x).Fits w ((F₀).mixed cut₀) ∧
      Source ((v).retainedHub b x) value (C).lanes (((F₀).received cut₀ scene₀ u.sceneFits).image m)) :
    ((v).retainedHub b x).Fits w ((C).casts first) ∧
      Source ((v).retainedHub b x) value (C).lanes (last ok m) :=by
  have before : (F₀).mixed cut₀≤(v).trunkEnd b :=
    (DescentResetTrunkCompactProgram.grow ..).trans (Nat.le_add_right ..)
  have below:=before.trans (((v).correction_cuts b).1.trans ((v).earlier b).2.1)
  have safe:=ProtocolRAMGeneratedWrite.fits_mono _ below prior.1
  have cut:=u.retained_order ok
  have stop : (C).casts first≤(C).endAddress first:=by
    obtain ⟨ca,cb,cc,cd,ce,cf,cg,ch⟩:=(C).order first;omega
  have kept : PrefixAgreement.Low ((F₀).mixed cut₀) (rk ok m) (((F₀).received cut₀ scene₀ u.sceneFits).image m):=
    fun i hi=>(u.ranked_trunk_frame ok m i (hi.trans_le before)).trans
      ((F₀).trunkScene_before cut₀ scene₀ u.sceneFits m ok.trunk i hi)
  exact ⟨(v).retained_hub_fits b scene₀ x (stop.trans_lt cut.2.2.2.2),
    u.from_rank_source ok m _ value safe (fun j=>
      (PrefixAgreement.expr _ _ _ _ (PrefixAgreement.inputEnd_of_fits _ prior.1) kept _).trans (prior.2 j))⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentDenseHostOrder DescentSIMDLookup
open DescentResetTrunkCompactPointer DescentResetFieldAssembler DescentCommonHost DescentResetTrunkIssue DescentActorRaster
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
open ThreeFlat.RAM PhysicalProcedure
open DescentDatedAddressBook DescentPackedZip DescentPackedColony
variable {a : PhysicalReset} {floor bw : ℕ} (u : a.DateInputs floor bw)
local notation "v" => a.successor
local notation "b₀" => a.rebased floor
local notation "C₀" => (v).setup
local notation "F₀" => (v).front
local notation "cut₀" => (v).actorEnd b₀
local notation "old₀" => (v).issuedScene b₀ u.earlier
local notation "c₀" => (F₀).peer.endAddress ((F₀).peers cut₀)
local notation "first₀" => (v).operandFloor b₀

/-- The authentic compacted trunk header supplies the hub correction in the
same final state as all the carried operand dictionaries. -/
theorem dated_primary_hub (ok : u.Ready) (m : Memory bw) (x : Fin (C₀).placement.blocks)
    (pitch : (C₀).lanes=(F₀).peer.lanes) (positive : 0<(F₀).peer.lanes) (field : 0<(F₀).metaBits)
    (stamp : (F₀).metaBits*7*(F₀).peer.lanes≤bw) (packing : (C₀).fieldBits*(F₀).peer.lanes≤bw)
    (marked : ∀r : Fin (F₀).newHosts,(F₀).preParent cut₀ old₀ u.sceneFits m (c₀+r.val)=
      ((DescentResetFieldAssembler.raw (F₀).metaBits ((originalTrunkRack B r).elim .blank (hostShape B))).val:Word bw)) :
    ((v).retainedHub b₀ x).Fits bw ((C₀).casts first₀) ∧ Source ((v).retainedHub b₀ x)
      (fun (h : Fin (F₀).newHosts) (_ : Fin (F₀).peer.groups)=>if ((originalTrunkRack B h).elim .blank (hostShape B)).core then (0:Cell (C₀).fieldBits) else 1)
      (C₀).lanes (((C₀).code first₀ bw u.bank u.laws).image (u.beforeSetupImage ok m)) :=by
  have first : (F₀).mixed cut₀≤(v).trunkEnd b₀ :=
    (DescentResetTrunkCompactProgram.grow ..).trans (Nat.le_add_right ..)
  have row:=dated_hub_source B (F₀) cut₀ old₀ u.sceneFits m (((F₀).received cut₀ old₀ u.sceneFits).image m)
    (C₀).fieldBits positive field stamp packing (first.trans_lt ok.trunk) marked (fun _ _=>rfl)
  apply u.dated_marked_at ok m x _
  refine ⟨row.1,?_⟩
  rw [pitch]
  exact row.2

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
