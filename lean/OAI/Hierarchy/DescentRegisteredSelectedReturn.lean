import OAI.Hierarchy.DescentRegisteredOrdinaryMemories
import OAI.Hierarchy.DescentRegisteredReturnedVenue
import OAI.Hierarchy.DescentRegisteredOrdinaryPeerRoom
import OAI.Hierarchy.DescentSelectedOrdinaryReturn
import OAI.Hierarchy.DescentRegisteredSignedReturn

namespace OAI
/-! # The returned venue on the same registered ordinary date as the original selected donor board -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentPacking.PackedMatch.Local DescentGroupPeerOrder DescentColonies DescentPackedColony DescentPackedExchange DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
namespace DatePorts
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {d k i z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {prevWorld : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {n : Normalize ((T.result he).state choice)}
    {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (prior : DatePorts) (ticket : OrdinaryLink prevWorld he T choice n next)
    (op : RotorSpec) (gain tail p f drift degree payload seats root : ℕ)
    (ordinary : ℕ→Dated.Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op gain k i p tail drift degree payload seats prior
local notation "base" => (books).onTicket ticket gain tail p f payload seats prior.venue.lanes prior.io.roster ordinary
local notation "floor" => (base).stageStart root

local notation "v" => ordinaryModel prior ticket op gain tail p f drift degree payload seats root ordinary

local notation "A" => (base).registeredEntry prior floor
local notation "match₀" => (base).registered_match prior floor (Nat.le_max_left prior.argumentsPerNode (S.retainedArgumentsAt G drift))
local notation "sh" => (base).registered_geometry prior floor
local notation "B" => (v).reachedSources floor

variable (w : ℕ) (shelf header : ℕ) (pos : 0<k)
variable (room : OrdinaryCodeRoom prior ticket op gain tail p f drift degree payload seats root ordinary w)
local notation "steps" => (v).issuedSteps root prior (A) room.signed w (match₀) (sh) room.blocks room.paths
  room.slots room.chip room.endFit room.packed room.radix room.funded


local notation "digits" => (v).signedInput floor room.signed
local notation "date₀" => DonorDate.atDate G S gain k i p
local notation "depot" => (v).donorEnd floor
local notation "sources" => (⟨prior.archive.count,prior.io.roster,prior.io.hubs⟩:DescentOrdinaryVenueReturn.Sources)
local notation "pg" => (⟨0,Nat.mul_pos (by decide : 0<7) room.slots⟩:Fin (7*(v).vector.operands))


variable (exec:OrdinaryExecutionRoom prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header room)
local notation "rot" => ((date₀).schedule (v).payload (v).seats (v).bitsPerField).rotationEnd prior.io.roster floor
local notation "meter" => (date₀).counter (v).payload rot header
local notation "readAt" => (v).rasterEnd floor
local notation "args" => (v).venue.operands B readAt
local notation "ready" => (v).metaStart floor
local notation "measure" => (⟨(v).prior.placement.wire,(v).prior.placement.z,(v).prior.placement.hist⟩:Dated.Measures)


local notation "donor" m:arg => ordinaryDonorMemory prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m
local notation "wired" m:arg => ordinarySignedMemory prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m
local notation "before" m:arg => (v).peerEntry root shelf header prior.io prior.archive.count digits steps date₀ pos exec m
local notation "peered" m:arg => (v).afterPeer root shelf header prior.io prior.archive.count digits steps date₀ pos exec m
local notation "paid" => (v).materialEnd floor
local notation "nextPeer" => (v).peerTail floor
local notation "mark_" => (v).markEnd floor
local notation "after" => (v).signedEnd floor
local notation "now" m:arg => (steps).arguments.image (wired m)


local notation "extra" => (base).argumentUnitFrom prior floor
local notation "hs" hv:arg => prevWorld.vertex.trans (Fin.castLEEmb hv)
local notation "realRoster" hv:arg => hostRotor (hs hv) (hostRoster prevWorld.placement ((hs hv).trans Fin.valEmbedding))

private theorem selectedPeerRooms (m : Memory w)
    (oldD : (v).area.D=D) (newD : (v).venue.degree=D') :
    let H := (v).area.H
    let R := (v).venue.hosts
    let roof := DescentOrdinaryVenueReturn.roof paid H D R D'
    (∀ j, j<roof → (now m) j=(DescentOrdinaryVenueReturn.phase sources paid k H D R D' w).image (before m) j) ∧
    (DescentOrdinaryPeerRows.peers paid H D R D').base+R*D'≤roof ∧
    (DescentOrdinaryVenueReturn.hubs paid H D R D').base+R≤roof ∧
    (DescentOrdinaryPeerCount.newCount paid H D R D').base<roof := by
  let bounds (oldDegree newDegree : ℕ) :=
    let H := (v).area.H
    let R := (v).venue.hosts
    let roof := DescentOrdinaryVenueReturn.roof paid H oldDegree R newDegree
    (∀ j, j<roof → (now m) j=(DescentOrdinaryVenueReturn.phase sources paid k H oldDegree R newDegree w).image (before m) j) ∧
    (DescentOrdinaryPeerRows.peers paid H oldDegree R newDegree).base+R*newDegree≤roof ∧
    (DescentOrdinaryVenueReturn.hubs paid H oldDegree R newDegree).base+R≤roof ∧
    (DescentOrdinaryPeerCount.newCount paid H oldDegree R newDegree).base<roof
  apply (congrArg₂ bounds oldD newD).mp
  have ranges := ordinary_peer_ranges prior ticket op gain tail p f drift degree payload seats root ordinary exec.late.peers
  obtain ⟨_,_,peerFrame,argFrame⟩ := ordinary_retained_memories prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m
  obtain ⟨_,_,peerSigned⟩ := (v).signed_stage_paid floor
  refine ⟨?_,ranges⟩
  intro j hj
  exact (argFrame j (hj.trans_le peerSigned)).trans (peerFrame j hj)

private theorem selectedWireRoom (newCap:(v).venue.cap=next.placement.cap) :
    ∀ (x:Block k) (j:Fin (2*next.placement.cap)),
      ((v).reachedWire floor x.val j.val).base+(v).venue.hosts*chunks (S.groupCount (i+1)) (v).venue.signedLanes ≤ after := by
  intro x j
  let b : Fin (v).signed.blocks := ⟨x.val,x.isLt⟩
  let l : Fin (2*(v).signed.cap) := j.cast (congrArg (2*·) newCap.symm)
  obtain ⟨hi,n⟩ := (v).signed.complete_page mark_ b l
  change ((v).reachedWire floor b.val l.val).base+_≤_
  rw [(v).reachedWire_at]
  exact (Nat.add_le_add_left n _).trans hi

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1400000 in
theorem returned_from_selected (m:Memory w)(oldFit:Fintype.card prevWorld.V≤(v).area.H)
    (pick:(prevWorld.placement.stage.result he).Choice)
    (board:(v).SelectedBoard oldFit (realRoster oldFit) pick (donor m) (steps).parts)(choiceEq:HEq pick choice)
    (age:i<S.length)(radix:S.radix=2^k)
    (old:stageVenue prevWorld oldFit prior.io (v).area.lanesAt (v).venue.paidBits root
      (prevWorld.venueRoster oldFit) m)
    (oldWires:∀(x:Block k)(j:Fin (2*prevWorld.placement.cap)),(prior.io.wire x.val j.val).base+
      (v).area.H*chunks (S.groupCount i) (v).area.lanesAt≤root)
    (oldCount:m prior.archive.count.base=(Fintype.card prevWorld.V:Word w))
    (countAt:prior.archive.count.base<root)(rotation:root≤rot)(donorFloor:root≤depot)
    (past:(steps).parts.base+(steps).parts.size≤depot)
    (oldD:(v).area.D=D)(newD:(v).venue.degree=D')(newCap:(v).venue.cap=next.placement.cap)
    (inlet:(A).Room (v) floor w)(gather:((A).directory (v) floor match₀).refs.Room w ((v).vectorStart floor))
    (origin:(v).TicketAdmission floor w room.signed (A) match₀ pg)(reach:(v).preparedUntil floor<2^w)
    (precision:prevWorld.placement.wire*(prevWorld.placement.z*G.b)*prevWorld.placement.cap<2^(v).venue.paidBits)
    (oldPos:0<(v).area.lanesAt)(actorPos:0<(v).rasterLanes)(paidPos:0<(v).venue.paidLanes)
    (wirePos:0<(v).venue.signedLanes)(hosts:0<(v).venue.hosts)(rows:0<chunks (S.groupCount (i+1)) (v).venue.paidLanes)
    (wires:∀wide:Fintype.card next.V≤(v).venue.hosts,∀(x:Block k)(j:Fin (2*next.placement.cap)),
      Reads ((v).reachedWire floor x.val j.val) (fun h g=>DescentSignedCableCodec.encode
        (Prepare.signed next.placement (next.order.trans Fin.valEmbedding) S next.valid (Function.Embedding.refl _)
          (next.vertex.trans (Fin.castLEEmb wide)) x j h g)) (v).venue.signedLanes (wired m)):
    returnedVenue prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m:=by
  intro target
  obtain ⟨donorFrame,preFrame,_,argFrame⟩:=ordinary_retained_memories prior ticket op gain tail p f drift
    degree payload seats root ordinary w shelf header pos room exec m
  have beforeRoot:=fun j hj=>(v).peer_entry_low root shelf header prior.io prior.archive.count digits steps date₀ pos exec
    m j hj rotation donorFloor
  have oldVenue:=stageVenue_below prevWorld oldFit prior.io (v).area.lanesAt (v).venue.paidBits root
    (prevWorld.venueRoster oldFit) m (before m) old oldWires beforeRoot
  obtain ⟨donorPaid,paidPeer,peerSigned⟩:=(v).signed_stage_paid floor
  have rootPaid:=donorFloor.trans donorPaid
  have rootSigned:=rootPaid.trans (paidPeer.trans peerSigned)
  obtain ⟨headerFrame,peerFence,hubFence,countFence⟩ := selectedPeerRooms prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m oldD newD
  have fin_:= (A).inlet_order (v) floor
  have extent : (A).priorStart (v) floor≤(v).refsStart floor:=by
    exact (fin_.2.1.trans (fin_.2.2.1.trans (fin_.2.2.2.1.trans fin_.2.2.2.2))).trans (match₀).atRefs.le
  have ends_ : (A).priorStart (v) floor≤(v).endAddress floor:=by
    obtain ⟨a,b⟩:=(v).mount_order floor
    obtain ⟨c,d,e,f,g⟩:=(v).routed_order floor
    omega
  have hh : DescentOrdinaryVenueReturn.Room sources paid (v).area.H D (v).venue.hosts D' w:=by
    have same : DescentOrdinaryVenueReturn.Room sources paid (v).area.H (v).area.D (v).venue.hosts (v).venue.degree w := exec.late.peers
    simpa only [oldD,newD] using same
  have peerRoof : DescentOrdinaryVenueReturn.roof paid (v).area.H D (v).venue.hosts D' = nextPeer := by
    change _ = DescentOrdinaryVenueReturn.roof paid (v).area.H (v).area.D (v).venue.hosts (v).venue.degree
    rw [oldD,newD]
  have ceiling : (A).priorStart (v) floor<2^w:=ends_.trans_lt room.endFit
  apply (v).selected_ordinary_venue («floor»:=floor) (wide:=oldFit) (targetFit:=target)
    (input:=prior.io) (priorCount:=prior.archive.count) (parts:=(steps).parts) («extra»:=extra)
    (choice:=pick) (m:=donor m) (board_:=board) (sameChoice:=choiceEq) rfl rfl rfl newD newCap rfl room.funded age radix
    root (before m) (wired m) (now m) oldVenue (fun a h=>preFrame a (h.trans_le rootPaid)) _ inlet.venue ceiling
    precision oldPos rootPaid (paidPeer.trans (peerSigned.trans exec.late.arguments.1))
    ends_ (fun a h=>(argFrame a (h.trans_le rootSigned)).trans (preFrame a (h.trans_le rootPaid))) _
    ((beforeRoot _ countAt).trans oldCount) hh _ _ after exec.late.arguments.1 argFrame _ _ _ _ (wires target)
    actorPos paidPos wirePos hosts rows room.result.venue
  · intro z
    have inside:=exec.late.material.sourceSize
    apply donorFrame
    exact (Nat.add_lt_add_left ((row _ _ _ z).isLt.trans_le inside) (steps).parts.base).trans_le past
  · exact ordinary_saved_receiver prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec
      inlet gather origin reach m
  · exact peerRoof.le.trans (peerSigned.trans exec.late.arguments.1)
  · exact headerFrame
  · exact peerFence
  · exact hubFence
  · exact countFence
  · exact selectedWireRoom prior ticket op gain tail p f drift degree payload seats root ordinary newCap

set_option maxHeartbeats 900000 in
/-- The physical cable pages are read directly from the signed scan of this board. -/
theorem returned_on_board (m:Memory w)(oldFit:Fintype.card prevWorld.V≤(v).area.H)
    (pick:(prevWorld.placement.stage.result he).Choice)
    (board:(v).SelectedBoard oldFit (realRoster oldFit) pick (donor m) (steps).parts)(choiceEq:HEq pick choice)
    (age:i<S.length)(radix:S.radix=2^k)
    (old:stageVenue prevWorld oldFit prior.io (v).area.lanesAt (v).venue.paidBits root
      (prevWorld.venueRoster oldFit) m)
    (oldWires:∀(x:Block k)(j:Fin (2*prevWorld.placement.cap)),(prior.io.wire x.val j.val).base+
      (v).area.H*chunks (S.groupCount i) (v).area.lanesAt≤root)
    (oldCount:m prior.archive.count.base=(Fintype.card prevWorld.V:Word w))
    (countAt:prior.archive.count.base<root)(rotation:root≤rot)(donorFloor:root≤depot)
    (past:(steps).parts.base+(steps).parts.size≤depot)
    (oldD:(v).area.D=D)(newD:(v).venue.degree=D')
    (inlet:(A).Room (v) floor w)(gather:((A).directory (v) floor match₀).refs.Room w ((v).vectorStart floor))
    (origin:(v).TicketAdmission floor w room.signed (A) match₀ pg)(reach:(v).preparedUntil floor<2^w)
    (precision:prevWorld.placement.wire*(prevWorld.placement.z*G.b)*prevWorld.placement.cap<2^(v).venue.paidBits)
    (oldPos:0<(v).area.lanesAt)(actorPos:0<(v).rasterLanes)(paidPos:0<(v).venue.paidLanes)
    (wirePos:0<(v).venue.signedLanes)(hosts:0<(v).venue.hosts)(rows:0<chunks (S.groupCount (i+1)) (v).venue.paidLanes)
    (fixed:(v).withIssuedSigned=v)(cash:(v).SignedRoom floor w)(safe:(v).area.Space prior.io w floor):
    returnedVenue prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m:=by
  have newCap:(v).venue.cap=next.placement.cap:=(congrArg (fun z:PhysicalOrdinary F P=>z.signed.cap) fixed).symm
  have srcDegree:(v).signed.degree=prevWorld.placement.degree:=
    (congrArg (fun z:PhysicalOrdinary F P=>z.signed.degree) fixed).symm
  apply returned_from_selected prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header
    pos room exec m oldFit pick board choiceEq age radix old oldWires oldCount countAt rotation donorFloor past
    oldD newD newCap inlet gather origin reach precision oldPos actorPos paidPos wirePos hosts rows
  intro newFit
  obtain ⟨keepDonor,keepBefore,_,_⟩:=ordinary_retained_memories prior ticket op gain tail p f drift degree
    payload seats root ordinary w shelf header pos room exec m
  have keep (j:ℕ) (hj:j<root) : (donor m) j=m j:=
    (keepDonor j (hj.trans_le donorFloor)).symm.trans <|
      (keepBefore j (hj.trans_le (donorFloor.trans ((v).signed_stage_paid floor).1))).trans
        ((v).peer_entry_low root shelf header prior.io prior.archive.count digits steps date₀ pos exec m j hj rotation donorFloor)
  have oldHere:=stageVenue_below prevWorld oldFit prior.io (v).area.lanesAt (v).venue.paidBits root
    (prevWorld.venueRoster oldFit) m (donor m) old oldWires keep
  apply signed_at_registered prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos
    room exec m oldFit (realRoster oldFit) pick board choiceEq newFit age radix
    (extended_reciprocal prevWorld.placement (hs oldFit) ((hs oldFit).trans Fin.valEmbedding))
    fixed rfl cash _ _ past _ exec.late.peers exec.late.mark oldPos (newD.trans next.branch.symm)
    safe (v).venue.paidBits root oldHere oldWires ((keep _ countAt).trans oldCount) countAt donorFloor
  · rw [←srcDegree]
    exact exec.late.ranks
  · rw [←srcDegree]
    exact exec.late.material
  · intro h j
    let column:=Fin.cast prevWorld.branch j
    have read:=oldHere.2.1.roster h column
    have rank:(hs oldFit).trans Fin.valEmbedding=prevWorld.vertex.trans Fin.valEmbedding:=by ext u;rfl
    have adjBase : (steps).adjacency.base = (prior.io.ports D).roster.base := rfl
    rw [adjBase]
    simp only [prevWorld.branch,Reached.venueRoster,DescentHaloWalkRAM.number,column,
      Fin.val_cast,Fin.cast_cast,Fin.cast_refl,rank,DescentPackedColony.target,Nat.add_assoc,id_eq] at read ⊢
    exact read

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
