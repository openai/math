import OAI.Hierarchy.DescentOrdinarySignedArchiveRead

namespace OAI
/-! Physical predecessor actor and hub fields on the registered signed RAM. -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
namespace DatePorts
open DescentDatedPriorOperand DescentOperandStateBanks

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


open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentPrimitivePalette


open DescentPackedColony DescentColonies
open scoped Fin.CommRing
/-- The original incoming actor census and host flag survive the entire signed procedure. -/
theorem ordinary_signed_pose {countBits : ℕ} (m : Memory w)
    (wide : Fintype.card prevWorld.V≤(v).area.H)
    (priorPose : stageVenue prevWorld wide prior.io (v).area.lanesAt countBits root
      (prevWorld.venueRoster wide) m) :
    Reads (A).venue.actors (Prepare.actors prevWorld.placement (Function.Embedding.refl _)
      (prevWorld.vertex.trans (Fin.castLEEmb wide))) (A).clip.actorPitch (wired m) ∧
    ∀h : Fin (v).area.H,(wired m) ((A).venue.hub.base+h.val)=
      ((Census.hub prevWorld.placement (prevWorld.vertex.trans (Fin.castLEEmb wide)) h).val:Computability.VPVNP.BurstRAM.Word w):=by
  rcases priorPose with ⟨entered,_,actor,_,hus,hs,hub,_⟩
  have frame:=ordinary_signed_archive_frame prior ticket op gain tail p f drift degree payload seats root ordinary
    w shelf header pos room exec m
  constructor
  · intro cell
    have limit:=(Nat.add_lt_add_left
      ((row (v).area.H (S.groupCount i) (v).area.lanesAt cell).isLt.trans_le entered.srcRoom)
      prior.io.actors.base).trans_le entered.source.2.2
    exact (frame _ limit).trans (actor cell)
  · intro h
    have limit:=(Nat.add_lt_add_left (h.isLt.trans_le hs) prior.io.hubs.base).trans_le hus.2.2
    exact (frame _ limit).trans (hub h)

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
