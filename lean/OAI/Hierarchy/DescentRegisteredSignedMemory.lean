import OAI.Hierarchy.DescentOriginalSignedPhase
import OAI.Hierarchy.DescentRegisteredOrdinaryHeld

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
variable (w : ℕ) (shelf header : ℕ) (pos : 0<k)
variable (room : OrdinaryCodeRoom prior ticket op gain tail p f drift degree payload seats root ordinary w)
local notation "steps" => (v).issuedSteps root prior (A) room.signed w (match₀) (sh) room.blocks room.paths
  room.slots room.chip room.endFit room.packed room.radix room.funded


local notation "sources" => (⟨prior.archive.count,prior.io.roster,prior.io.hubs⟩:DescentOrdinaryVenueReturn.Sources)

variable (exec:OrdinaryExecutionRoom prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header room)
local notation "phys" => (v).withIssuedSigned
local notation "donors" m:arg => ordinaryDonorMemory prior ticket op gain tail p f drift degree payload seats root ordinary
  w shelf header pos room exec m
local notation "out" m:arg => ordinarySignedMemory prior ticket op gain tail p f drift degree payload seats root ordinary
  w shelf header pos room exec m

theorem ordinary_registered_signed (selected:(base).withIssuedSigned=base) :
    phys=v ∧ (v).venue.signedLanes=(v).signed.lanes:=by
  have shape : (v).signedLayout.format (v).payload=(v).signed:=
    congrArg (fun u:PhysicalOrdinary F P=>u.signed) selected
  constructor
  · change {v with signed:=(v).signedLayout.format (v).payload}=v
    rw [shape]
  · rfl

/-- Proof irrelevance of the finite chart lets the registered program use its
original witnesses while running the selected physical signed program. -/
theorem ordinary_signed_image (m:Memory w) (fixed:phys=v) :
    ((v).signedReturn floor prior.io prior.archive.count (steps).parts (steps).adjacency w).image
      (donors m)=out m:=by
  let plot (u:PhysicalOrdinary F P) (c:u.SignedChart) : Memory w :=
    let first:=(u.beforeSignedMaterial floor (steps).parts (steps).adjacency w).image (donors m)
    let peers:=(DescentOrdinaryVenueReturn.phase sources (u.materialEnd floor) k (v).area.H
      (v).area.D (v).venue.hosts (v).venue.degree w).image first
    (u.signedPhase floor c w).image ((u.mark floor prior.io w).image peers)
  have transport {x y:PhysicalOrdinary F P} (eqn:x=y) (a:x.SignedChart) (b:y.SignedChart) : plot x a=plot y b:=by
    subst y
    rfl
  exact transport fixed (v).issuedSignedChart room.signed

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
