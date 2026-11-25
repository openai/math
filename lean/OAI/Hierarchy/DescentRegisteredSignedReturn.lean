import OAI.Hierarchy.DescentRegisteredSignedMemory
import OAI.Hierarchy.DescentRegisteredSelectedBoard
import OAI.Hierarchy.DescentDatedSignedSelectedBoard

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch DescentPacking DescentCompiler DescentKernelHistory.BitDescription
open DescentPackedProfileWide DescentPackedProfileWindow DescentPackedProfileArchive DescentTerminalEpochDecoder
open DescentTerminalEpochChart DescentPackedColony DescentStageEdgeReceipt DescentGroupPeerOrder DescentHostDirectory
open DescentHaloWalkRAM
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

local notation "phys" => (v).withIssuedSigned
local notation "ss" => (phys).signed
local notation "donors" m:arg => ordinaryDonorMemory prior ticket op gain tail p f drift degree payload seats root ordinary
  w shelf header pos room exec m
local notation "out" m:arg => ordinarySignedMemory prior ticket op gain tail p f drift degree payload seats root ordinary
  w shelf header pos room exec m

/-- Both incidence directions and all padded sheets of the returned ordinary
stage at the exact registered post-signed memory. -/
theorem signed_at_registered (m:Memory w) (oldFit:Fintype.card prevWorld.V≤(v).area.H)
    (R:Fin (v).area.H→Fin (original).degree→Option (Fin (v).area.H)) (pick:((original).stage.result he).Choice)
    (board:(v).SelectedBoard oldFit R pick (donors m) (steps).parts)
    (chosen:HEq pick choice) (newFit:Fintype.card next.V≤(v).venue.hosts) (age:i<S.length) (radix:S.radix=2^k)
    (symmetric:∀b a j,R b j=some a→∃l,R a l=some b)
    (fixed:phys=v) (pitch:(v).venue.signedLanes=(v).signed.lanes)
    (cash:(v).SignedRoom floor w)
    (pre:DescentDatedAddressBook.PriorHeader.Room (steps).adjacency (v).area.H (v).signed.groups
      (v).signed.lanes (original).degree ((v).donorEnd floor) w)
    (material:(v).MaterialRoom ((v).materialStart floor) (steps).parts
      (DescentDatedAddressBook.PriorHeader.reverseRank (v).area.H (v).signed.groups (v).signed.lanes
        (original).degree ((v).donorEnd floor)) w)
    (past:(steps).parts.base+(steps).parts.size≤(v).donorEnd floor)
    (existing:∀h j,(donors m) ((steps).adjacency.base+h.val*(original).degree+j.val)=(number (R h j):Word w))
    (geometry:DescentOrdinaryVenueReturn.Room sources ((v).materialEnd floor) (v).area.H
      (v).area.D (v).venue.hosts (v).venue.degree w)
    (mark:(v).MarkRoom floor prior.io w) (oldMarks:0<(v).markShape.oldLanes)
    (newDegree:(v).venue.degree=next.placement.degree) (safe:(v).area.Space prior.io w floor)
    (precision lower:ℕ) (old:stageVenue prevWorld oldFit prior.io (v).markShape.oldLanes precision lower
      (prevWorld.venueRoster oldFit) (donors m))
    (wires:∀(x:Fin (2^k))(j:Fin (2*(original).cap)),(prior.io.wire x.val j.val).base+
      (v).area.H*chunks (S.groupCount i) (v).markShape.oldLanes≤lower)
    (countRead:(donors m) prior.archive.count.base=(Fintype.card prevWorld.V:Word w))
    (countLow:prior.archive.count.base<lower) (place:lower≤(v).donorEnd floor) :
    ∀(x:Fin (2^k))(j:Fin (2*next.placement.cap)),
      Reads ((v).reachedWire floor x.val j.val) (fun h g=>DescentSignedCableCodec.encode
        (Prepare.signed next.placement (next.order.trans Fin.valEmbedding) S next.valid
          (Equiv.refl (Fin (S.groupCount (i+1)))).toEmbedding (next.vertex.trans (Fin.castLEEmb newFit))
          x j h g)) (v).venue.signedLanes (out m):=by
  have claimed:=(v).signed_from_match (oldFit:=oldFit) (R:=R) (selected:=pick) (m:=donors m)
    (parts:=(steps).parts) («B»:=board) (choiceEq:=chosen) (wide:=newFit) (age:=age) (radix:=radix)
    (reciprocal:=symmetric) («floor»:=floor) (input:=prior.io) (count:=prior.archive.count)
    (adj:=(steps).adjacency) (by simpa only [fixed] using cash) (by rw [fixed]; exact pre)
    (by rw [fixed]; exact material) (by simpa only [fixed] using past) existing
    (by simpa only [fixed] using geometry) (by simpa only [fixed] using mark) (by simpa only [fixed] using oldMarks)
    newDegree safe precision lower (by rw [fixed]; exact old) (by rw [fixed]; exact wires) countRead
    countLow (by simpa only [fixed] using place)
  intro x j
  have bank:=congrArg (fun u:PhysicalOrdinary F P=>u.reachedWire floor x.val j.val) fixed
  have lanes: (v).venue.signedLanes=(phys).signed.lanes:=pitch.trans
    (congrArg (fun u:PhysicalOrdinary F P=>u.signed.lanes) fixed).symm
  rw [←bank,(phys).reachedWire_at floor x j,lanes,←ordinary_signed_image prior ticket op gain tail p f drift
    degree payload seats root ordinary w shelf header pos room exec m fixed]
  exact claimed.2.1 x j

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
