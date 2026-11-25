import OAI.Hierarchy.DescentOrdinaryArgumentClippedFrame
import OAI.Hierarchy.DescentRegisteredOrdinaryHeld

namespace OAI
/-! # The donor and peer registers survive the genuine numbered ordinary material, mark and signed scans -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
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


local notation:max "donor" m:arg => ordinaryDonorMemory prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m
local notation:max "wired" m:arg => ordinarySignedMemory prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m
local notation:max "before" m:arg => (v).peerEntry root shelf header prior.io prior.archive.count digits steps date₀ pos exec m
local notation:max "peered" m:arg => (v).afterPeer root shelf header prior.io prior.archive.count digits steps date₀ pos exec m
local notation "paid" => (v).materialEnd floor
local notation "nextPeer" => (v).peerTail floor
local notation "mark_" => (v).markEnd floor
local notation "after" => (v).signedEnd floor
local notation:max "now" m:arg => (steps).arguments.image (wired m)

theorem ordinary_retained_memories (m:Memory w) :
    (∀a<depot,wired m a=donor m a) ∧
    (∀a<paid,wired m a=before m a) ∧
    (∀a<nextPeer,wired m a=peered m a) ∧
    (∀a<after,now m a=wired m a) :=by
  let pre:=before m
  let peer:=peered m
  let marked:=((v).mark floor prior.io w).image peer
  have original:=(v).before_signed_any floor (steps).parts (steps).adjacency exec.late.ranks exec.late.material (donor m)
  have headerRun:=DescentOrdinaryVenueReturn.any sources paid k (v).area.H (v).area.D
    (v).venue.hosts (v).venue.degree w pre exec.late.peers
  have flag:=(v).mark_any floor prior.io exec.late.mark peer
  have mapped:=(v).signed.calibrated mark_
  have finished:=(v).signed.phase_any digits mark_ w marked exec.late.signed (mapped.le.trans_lt exec.late.signedRoom)
  obtain ⟨donorCut,peerCut,_⟩:=(v).signed_stage_paid floor
  have markCut:=(v).markShape.low nextPeer
  have keepPeer (a:ℕ) (inPeer:a<nextPeer):wired m a=peer a:=
    (finished.2.1 a (.inl (inPeer.trans_le markCut))).trans ((flag.2 a (.inl inPeer)))
  have keepOriginal (a:ℕ) (inMat:a<paid):wired m a=pre a :=
    (keepPeer a (inMat.trans_le peerCut)).trans (headerRun.2 a (.inl inMat))
  exact ⟨fun a low=>(keepOriginal a (low.trans_le donorCut)).trans (original.2 a (.inl low)),
    keepOriginal,keepPeer,fun a low=>(exec.late.arguments.2 (wired m)).2 a (.inl low)⟩

/-- All clipped old-actor and party reports stay readable while the reference, birth and argument books are written. -/
theorem ordinary_saved_receiver (inlet:(A).Room (v) floor w)
    (gather:((A).directory (v) floor match₀).refs.Room w ((v).vectorStart floor))
    (origin:(v).TicketAdmission floor w room.signed (A) match₀ pg)
    (reach:(v).preparedUntil floor<2^w)
    (m:Memory w)(j:ℕ)(inside:j<(A).priorStart (v) floor) :
    now m j=((A).clip.phase (A).venue ((v).signedEnd floor) w).image (wired m) j:=by
  have slices: (v).origin.grainBase ((v).routedStart floor)=(v).preparedUntil floor:=by
    apply (v).grain_after_sources
    exact ((base).fundedFrom prior floor).origin_reservation
  have beforeOutput : (v).preparedUntil floor≤(v).origin.outputBase ((v).routedStart floor):=by
    rw [←slices];exact Nat.le_add_right ..
  have original:=(v).ticket_preparation_any floor w room.signed (A) match₀ sh room.blocks pg origin reach
  have bounds:=fun j f=>ProtocolRAMGeneratedWrite.fits_mono _ beforeOutput ((original (fun _=>0)).2 j f)
  exact (v).argument_clipped_frame floor A match₀ _ _ room.chip sh room.endFit room.packed
    inlet gather bounds (fun m=>⟨(original m).1.run,by rw [slices];exact (original m).1.frame⟩)
    (wired m) j inside

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
