import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.DescentRegisteredMatcherBanks
import OAI.Hierarchy.DescentRegisteredOrdinaryStep
import OAI.Hierarchy.DescentDatedOrdinaryHeld
import OAI.Hierarchy.DescentDatedTicketPreparationTotal
import OAI.Hierarchy.DescentDatedSignedAny

namespace OAI
/-! Total execution and range preservation of the actual registered ordinary instruction. -/
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

/-- The arbitrary-input window used by the registered move. -/
abbrev OrdinaryExecutionRoom := PhysicalOrdinary.Room (v) root shelf header prior.io prior.archive.count
  digits steps date₀

/-- All three deferred scans have their native program and frame already fixed by the earlier physical entry. -/
theorem ordinary_result_runs
    (ranks:PriorHeader.Room (A).venue.adjacency (v).area.H (v).signed.groups (v).signed.lanes (v).signed.degree depot w)
    (material:(v).MaterialRoom ((v).materialStart floor) (A).venue.panel
      (PriorHeader.reverseRank (v).area.H (v).signed.groups (v).signed.lanes (v).signed.degree depot) w)
    (peers:DescentOrdinaryVenueReturn.Room sources ((v).materialEnd floor) (v).area.H (v).area.D (v).venue.hosts (v).venue.degree w)
    (mark:(v).MarkRoom floor prior.io w) (wire:(v).SignedRoom floor w) (inlet:(A).Room (v) floor w)
    (gather:((A).directory (v) floor match₀).refs.Room w ((v).vectorStart floor))
    (origin:(v).TicketAdmission floor w room.signed (A) match₀ pg)
    (reach:(v).preparedUntil floor<2^w) (primitive:(v).PrimitiveRoom floor (A) w) :
    (v).ResultRuns floor prior.io prior.archive.count digits steps :=by
  have slices: (v).origin.grainBase ((v).routedStart floor)=(v).preparedUntil floor:=by
    apply (v).grain_after_sources
    exact ((base).fundedFrom prior floor).origin_reservation
  have before: (v).preparedUntil floor≤(v).origin.outputBase ((v).routedStart floor):=by
    rw [←slices];exact Nat.le_add_right ..
  have original:=(v).ticket_preparation_any floor w room.signed (A) match₀ sh room.blocks pg origin reach
  have bounds:=fun j f=>ProtocolRAMGeneratedWrite.fits_mono _ before ((original (fun _=>0)).2 j f)
  have phases:=(v).result_inputs floor prior.io (A) match₀ room.paths _ _ room.chip sh room.endFit room.packed
    room.radix room.funded inlet gather bounds (fun m=>⟨(original m).1.run,by
      rw [slices];exact (original m).1.frame⟩)
  have earlier:=(v).signed_prior_sources floor w room.signed wire
  have geo:=(v).signed_peer_inputs floor w room.signed wire
  have physical:=(v).signed.fits_from_prior digits ((v).markEnd floor) earlier wire.room
    ((v).signed.peer_head_fits digits _ wire.room geo) ((v).signed.signed_header_fits digits _ earlier wire.room)
    ((v).signed.flags_fits digits _ earlier wire.room)
  exact ⟨ranks,material,peers,mark,physical,(Nat.le_add_right ..).trans_lt wire.room,phases.1,phases.2,
    (v).primitive_input floor (A) match₀ room.radix primitive⟩

local notation "a₀" => (date₀).schedule (v).payload (v).seats (v).bitsPerField
local notation "rom₀" => (a₀).prepareAt prior.io.roster floor
local notation "rot₀" => (a₀).rotationEnd prior.io.roster floor
local notation "matched" => (date₀).matcherOutput (v).payload (v).seats prior.io rom₀

/-- The two tables read by the external profile loader and the count scan lie in
the true matcher range; the donor and counter use those same matched banks. -/
theorem ordinary_execution
    (geometry:(v).area=a₀)
    (shelfRoom:(DescentPackedProfileInstall.sourceBank shelf (v).profileRepack.seats (v).profileRepack.oldLanes).Fits w root)
    (matcher:(a₀).Space prior.io w floor)
    (charge:(date₀).PhaseRoom (v).payload rot₀ w matched ∧ ((date₀).counter (v).payload rot₀ header).Room w)
    (suffix:(v).ResultRuns floor prior.io prior.archive.count digits steps)
    (before:rot₀≤(v).primitiveEnd floor) (ceiling:(v).fullEnd root<2^w) :
    OrdinaryExecutionRoom prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header room:=by
  have late:(v).primitiveEnd floor≤(v).fullEnd root:=by
    exact (Nat.le_add_right ((v).primitiveEnd floor) (2^(v).countBits)).trans
      ((Nat.le_add_right _ (v).area.batch).trans (Nat.le_add_right _ 1))
  have both:=(a₀).match_banks prior.io floor ((v).primitiveEnd floor) w before (late.trans_lt ceiling)
  exact ⟨shelfRoom,by rw [geometry];exact both.1,matcher,charge.1,suffix,by rw [geometry];exact both.2,ceiling,charge.2⟩

variable (exec:OrdinaryExecutionRoom prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header room)
def ordinaryOutput (m:Memory w) := (v).dateOutput root shelf header prior.io prior.archive.count digits (B) steps room.result date₀ pos exec m

theorem ordinary_output (m:Memory w) :
    (ordinaryDate prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room).Runs m
      (ordinaryOutput prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m) ∧
    (ordinaryDate prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room).cheap :=
  (v).date_any root shelf header prior.io prior.archive.count digits (B) steps room.result date₀ pos exec m

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
