import OAI.Hierarchy.DescentRegisteredOrdinaryHeld
import OAI.Hierarchy.DescentDatedOriginalSelectedVisit

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch DescentPacking DescentCompiler DescentKernelHistory.BitDescription
open DescentPackedProfileWide DescentPackedProfileWindow DescentPackedProfileArchive DescentTerminalEpochDecoder
open DescentTerminalEpochChart DescentPackedColony DescentStageEdgeReceipt DescentGroupPeerOrder DescentHostDirectory
open DescentSixParty.StarKeys
open scoped Classical Fin.CommRing
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
namespace DatePorts
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule}
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


local notation "a₀" => (date₀).schedule payload seats (v).bitsPerField
local notation "entered" m:arg => ((v).archivePhase root shelf w).image m
local notation "original" => prevWorld.placement
local notation "gid" => Equiv.refl (Fin (S.groupCount i))
local notation "native" => prevWorld.order.trans Fin.valEmbedding
local notation "names" wide:arg => GroupStage.plane (v).hostNumbers wide
local notation "earlyRank" wide:arg => groupRank ((gid).toEmbedding.trans Fin.valEmbedding) ((names wide).trans Fin.valEmbedding)
local notation "oldRotor" wide:arg => hostRotor (names wide)
  (DescentGroupPeerOrder.hostRoster original ((names wide).trans Fin.valEmbedding))

private theorem same_match_image {a b:Dated.Ordinary} (eqn:a=b)
    (hk:0<a.k) (hk':0<b.k) (input:Dated.Operands) (meas:Dated.Measures) (addr w:ℕ)
    (first:a.Space input w addr) (second:b.Space input w addr) (m:Memory w) :
    (a.nativePhase G hk input meas w addr first).image m=(b.nativePhase G hk' input meas w addr second).image m:=by
  subst b
  rfl

set_option maxHeartbeats 900000 in
/-- The selected board on the very donor memory consumed by the numbered
date, with the real source address carried by its before-signed result steps. -/
theorem selected_meter_at_donor {Pin:Type} (m:Memory w) (pick:((original).stage.result he).Choice)
    (entry:Source Pin) (zeta:Pin→Bool) (wide:Fintype.card prevWorld.V≤(v).area.H)
    (width:DescentTerminalEpochBits.width entry.C≤(v).area.shapeAt.digit)
    (seen:(v).reachedReport prior.io floor wide (entered m) pick entry zeta width)
    (readback:∀j,(wideCell entry.pin zeta (v).area.shapeAt.digit width j).val=
      profileAt (inputNumber he original (gid).toEmbedding (names wide))
        ((scannedRows he (original).stage).profile pick) j)
    (chosen:HEq choice pick)
    (named:(original).SiteNamed (earlyRank wide) ∧ ∀x y,native x<native y ↔ originalId W.graph.Edge x<originalId W.graph.Edge y)
    (budget:Fintype.card (NativePair W.graph W.core (scanHomeAt he (original).stage)
      (scanColorAt he (original).stage) (original).cap)*(G.C+8+8*G.k)<2^w)
    (venue:stageVenue prevWorld wide prior.io (v).area.lanesAt (v).bitsPerField floor
      (prevWorld.venueRoster wide) (entered m))
    (dated:ticket.donorDate=date₀) (geometry:(v).area=a₀)
    (started:header≤rot) (live:0<(date₀).amount) {ratio:ℕ} (overhead:w≤ratio*payload)
    (memory:ticket.wholeDonorEnd (v).short (v).profile (v).area.H payload rot≤2^w)
    (grain:(original).stage.z=S.grainAt G.b p i) :
    Nonempty ((v).SelectedBoard wide (oldRotor wide) pick
      (ordinaryDonorMemory prior ticket op gain tail p f drift degree payload seats root ordinary
        w shelf header pos room exec m) (steps).parts) ∧
    MeterRows ticket header ratio meter (ordinaryDonorMemory prior ticket op gain tail p f drift degree payload seats
      root ordinary w shelf header pos room exec m) :=by
  have safe:(v).area.Space prior.io w floor:=geometry.symm ▸ exec.matcher
  have shortShape:(v).short=max (k+3) (Nat.clog 2 ((original).degree+1)):=by
    change max (k+3) (Nat.clog 2 ((date₀).degree+1))=_
    rw [←dated]
    rfl
  have price:(v).unit=ticket.installedDonorWidth (v).short (v).profile:=by
    rw [shortShape]
    change (date₀).amount=_
    rw [←dated]
    rfl
  have payloadEq : (v).payload = payload := rfl
  have seatsEq : (v).seats = seats := rfl
  have scheduleEq : (v).area = (date₀).schedule (v).payload (v).seats (v).bitsPerField := by
    rw [payloadEq, seatsEq]; exact geometry
  have size:header≤(v).area.rotationEnd prior.io.roster floor:=by rw [scheduleEq]; exact started
  have roof:ticket.wholeDonorEnd (v).short (v).profile (v).area.H payload
      ((v).area.rotationEnd prior.io.roster floor)≤2^w:=by
    rw [scheduleEq]
    exact memory
  have posted:=(v).board_and_meter_of_observed_match prior.io floor wide (entered m) pick entry zeta width safe
    seen readback chosen named budget venue rfl price shortShape rfl size live overhead roof grain
  have same:=same_match_image (G:=G) geometry (original).fieldBits pos prior.io measure floor w safe exec.matcher (entered m)
  have identical : (ticket.donorDate.afterMatcher payload seats prior.io (v).bitsPerField floor w).image
      (((v).area.nativePhase G (original).fieldBits prior.io measure w floor safe).image (entered m))=
      ordinaryDonorMemory prior ticket op gain tail p f drift degree payload seats root ordinary
        w shelf header pos room exec m:=by
    rw [same,dated]
    rfl
  rw [←identical]
  constructor
  · exact posted.1
  · have meterEq : ticket.donorDate.counter (v).payload ((v).area.rotationEnd prior.io.roster floor) header = meter := by
      rw [dated,scheduleEq]
    rw [←meterEq]
    exact posted.2

theorem selected_at_donor {Pin:Type} (m:Memory w) (pick:((original).stage.result he).Choice)
    (entry:Source Pin) (zeta:Pin→Bool) (wide:Fintype.card prevWorld.V≤(v).area.H)
    (width:DescentTerminalEpochBits.width entry.C≤(v).area.shapeAt.digit)
    (seen:(v).reachedReport prior.io floor wide (entered m) pick entry zeta width)
    (readback:∀j,(wideCell entry.pin zeta (v).area.shapeAt.digit width j).val=
      profileAt (inputNumber he original (gid).toEmbedding (names wide))
        ((scannedRows he (original).stage).profile pick) j)
    (chosen:HEq choice pick)
    (named:(original).SiteNamed (earlyRank wide) ∧ ∀x y,native x<native y ↔ originalId W.graph.Edge x<originalId W.graph.Edge y)
    (budget:Fintype.card (NativePair W.graph W.core (scanHomeAt he (original).stage)
      (scanColorAt he (original).stage) (original).cap)*(G.C+8+8*G.k)<2^w)
    (venue:stageVenue prevWorld wide prior.io (v).area.lanesAt (v).bitsPerField floor
      (prevWorld.venueRoster wide) (entered m))
    (dated:ticket.donorDate=date₀) (geometry:(v).area=a₀)
    (started:header≤rot) (live:0<(date₀).amount) {ratio:ℕ} (overhead:w≤ratio*payload)
    (memory:ticket.wholeDonorEnd (v).short (v).profile (v).area.H payload rot≤2^w)
    (grain:(original).stage.z=S.grainAt G.b p i) :
    Nonempty ((v).SelectedBoard wide (oldRotor wide) pick
      (ordinaryDonorMemory prior ticket op gain tail p f drift degree payload seats root ordinary
        w shelf header pos room exec m) (steps).parts) :=by
  exact (selected_meter_at_donor prior ticket op gain tail p f drift degree payload seats root ordinary
    w shelf header pos room exec m pick entry zeta wide width seen readback chosen named budget venue
    dated geometry started live overhead memory grain).1

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
