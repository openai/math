import OAI.Hierarchy.DescentRegisteredSelectedBoard
import OAI.Hierarchy.DescentDonorCounterBetween

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch DescentPacking DescentCompiler DescentKernelHistory.BitDescription
open DescentPackedProfileWide DescentPackedProfileWindow DescentPackedProfileArchive DescentTerminalEpochDecoder
open DescentTerminalEpochChart DescentPackedColony DescentStageEdgeReceipt DescentGroupPeerOrder DescentHostDirectory
open scoped Classical Fin.CommRing
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
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
local notation "entered" m => ((v).archivePhase root shelf w).image m
local notation "original" => prevWorld.placement
local notation "gid" => Equiv.refl (Fin (S.groupCount i))
local notation "native" => prevWorld.order.trans Fin.valEmbedding
local notation "names" wide => GroupStage.plane (v).hostNumbers wide
local notation "earlyRank" wide => groupRank ((gid).toEmbedding.trans Fin.valEmbedding) ((names wide).trans Fin.valEmbedding)
local notation "oldRotor" wide => hostRotor (names wide)
  (DescentGroupPeerOrder.hostRoster original ((names wide).trans Fin.valEmbedding))

variable {age₀ grain₀ degree₀ : ℕ} {W₀ : MarkedWorld F d P bits}
    {first : Reached W₀ G q ε S k age₀ grain₀ degree₀ wire hist}

theorem ordinary_held_of_rows (m : Memory w) {ratio : ℕ}
    (rows : MeterRows ticket header ratio meter (ordinaryDonorMemory prior ticket op gain tail p f drift degree
      payload seats root ordinary w shelf header pos room exec m))
    (before : Path first prevWorld) (oldHeld : before.Held header m) (low : header<root)
    (rootAt : root≤rot) (charged : (meter).endAddr≤depot) :
    (before.ordinary ticket).Held header
      (ordinaryOutput prior ticket op gain tail p f drift degree payload seats root ordinary
        w shelf header pos room exec m) :=by
  let assessed:=ordinaryDonorMemory prior ticket op gain tail p f drift degree payload seats root ordinary
    w shelf header pos room exec m
  have kept : assessed header=m header :=
    (v).donor_input_low root shelf header prior.io prior.archive.count digits steps date₀ pos exec m header low rootAt
  have meterOrder:=DonorDate.dated_counter_between G S gain k i p payload rot header
  have fitsHeader : header<depot:=lt_of_le_of_lt (low.le.trans rootAt)
    (meterOrder.1.trans_lt (meterOrder.2.1.trans_le charged))
  have writes := (v).meter_input_low root shelf header prior.io prior.archive.count digits B steps room.result
    date₀ exec assessed
  apply MeterRows.advance ticket rows before
  · exact oldHeld.keep ((writes header fitsHeader).trans kept)
  · exact fun j hj=>writes j (hj.trans_le charged)

theorem ordinary_held_private {Pin:Type} (m:Memory w) (pick:(prevWorld.placement.stage.result he).Choice)
    (entry:Source Pin) (zeta:Pin→Bool) (wide:Fintype.card prevWorld.V≤(v).area.H)
    (width:DescentTerminalEpochBits.width entry.C≤(v).area.shapeAt.digit)
    (seen:(v).reachedReport prior.io floor wide (entered m) pick entry zeta width)
    (readback:∀j,(wideCell entry.pin zeta (v).area.shapeAt.digit width j).val=
      profileAt (inputNumber he original (gid).toEmbedding (names wide))
        ((scannedRows he prevWorld.placement.stage).profile pick) j)
    (chosen:HEq choice pick)
    (named:prevWorld.placement.SiteNamed (earlyRank wide) ∧ ∀x y,native x<native y ↔ originalId W.graph.Edge x<originalId W.graph.Edge y)
    (budget:Fintype.card (StarKeys.NativePair W.graph W.core (scanHomeAt he prevWorld.placement.stage)
      (scanColorAt he prevWorld.placement.stage) prevWorld.placement.cap)*(G.C+8+8*G.k)<2^w)
    (venue:stageVenue prevWorld wide prior.io (v).area.lanesAt (v).bitsPerField floor
      (prevWorld.venueRoster wide) (entered m))
    (dated:ticket.donorDate=date₀) (geometry:(v).area=a₀)
    (started:header≤rot) (live:0<(date₀).amount) {ratio:ℕ} (overhead:w≤ratio*payload)
    (memory:ticket.wholeDonorEnd (v).short (v).profile (v).area.H payload rot≤2^w)
    (grain:prevWorld.placement.stage.z=S.grainAt G.b p i)
    (before : Path first prevWorld) (oldHeld : before.Held header m) (low : header<root)
    (rootAt : root≤rot) (charged : (meter).endAddr≤depot) :
    (before.ordinary ticket).Held header
      (ordinaryOutput prior ticket op gain tail p f drift degree payload seats root ordinary
        w shelf header pos room exec m) :=by
  let assessed:=ordinaryDonorMemory prior ticket op gain tail p f drift degree payload seats root ordinary
    w shelf header pos room exec m
  have rows : MeterRows ticket header ratio meter assessed :=
    (selected_meter_at_donor prior ticket op gain tail p f drift degree payload seats root ordinary
      w shelf header pos room exec m pick entry zeta wide width seen readback chosen named budget venue
      dated geometry started live overhead memory grain).2
  exact ordinary_held_of_rows prior ticket op gain tail p f drift degree payload seats root ordinary
    w shelf header pos room exec m rows before oldHeld low rootAt charged

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
