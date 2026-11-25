import OAI.Hierarchy.DescentReturnedMetadataCells
import OAI.Hierarchy.DescentRegisteredOrdinaryHeaderWriter

namespace OAI
/-! # Both returned node rows and the arity digit on each genuine or vacant node -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 900000
set_option maxRecDepth 6000
open scoped Classical Fin.CommRing
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

open DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
local notation "current" m => (v).beforeReturn root shelf header prior.io prior.archive.count digits steps date₀ pos exec m
local notation "funded" m => (((v).venue.phase B ((v).rasterEnd floor) w).image (current m))

local notation "record" m => ordinaryMetadata prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m
local notation "chart" => (v).nodeChart
local notation "start" => (v).metaStart floor
local notation "pb" => (v).metadata.paidBits
local notation "sb" => (v).resolver.size+2
local notation "counts" => (fun x:Fin (chart).blocks=>(v).venue.metadataPaid B x.val)
local notation "spans" => (v).spanVectors floor


open DescentCompiler DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
variable [Fintype P] {R : ℕ} (desc : BitDescription n.result) (ord : Local desc)
local notation "ports" => DatePorts.ordinary v floor
variable (places : RangeRoom ports next desc) (shape : WorldShape p R desc)
local notation "atNode" => slotAt ports next desc ord places
local notation "lengthAt" x:arg j:arg h:arg g:arg =>
  (atNode x j h g).elim 0 (fun y=>(occurrences (shape.sites y.1) y.2).length)
local notation "flag" => RegisterTimeline.archiveFlag next desc ord ports places

omit [Fintype P] in
theorem header_arity_from_f6 (dates : ℕ→DateCode w) (m : Memory w) (wide : Fintype.card next.V≤(v).venue.hosts)
    (crop : (v).resolver.hosts≤(v).venue.hosts)
    (issued : returnedVenue prior ticket op gain tail p f drift degree payload seats root ordinary
      w shelf header pos room exec (DateCode.history dates m i))
    (words : Fin (chart).blocks→Fin (v).resolver.operands→Fin (chart).hosts→Fin (chart).groups→Cell ((sb)*(chart).nodes))
    (printed : ∀x j,Reads (spans x j) (words x j) (chart).lanes (record (DateCode.history dates m i)))
    (hp : 0<p)
    (mean : ∀x n j h g,(DescentOrdinaryAtomFieldRAM.ScalarOperand.take (a:=sb) n (words x j h g)).val=
      (atNode x n h g).elim 0 (fun y=>atSlot (shape.sites y.1) y.2 j.val 2))
    (argFit : ∀u n,((shape.sites u).recipe hp).arity n≤(v).resolver.operands)
    (mass : next.placement.wire*(next.placement.z*G.b)*next.placement.cap<2^(S.censusBits p))
    (width : (v).resolver.operands<2^(ports).operandBits) :
    HeaderArity prior ticket op gain tail p f drift degree payload seats root ordinary
      w shelf header pos room exec desc ord places shape hp dates m :=by
  apply returned_metadata_cells prior ticket op gain tail p f drift degree payload seats root ordinary
    w shelf header pos room exec desc ord places shape (DateCode.history dates m i) wide crop issued words printed
    _ hp _ _ mass (fun u n=>(argFit u n).trans_lt width)
  · intro x n h g
    cases physical : atNode x n h g with
    | none => exact Nat.zero_le _
    | some y => simpa only [physical,Option.elim_some,DescentRetainedRangeDigits.length _ _ hp] using argFit y.1 y.2
  · intro x n j h g y present
    have packed := mean x n j h g
    rw [present] at packed
    exact packed
  · intro x n j h g vacant
    apply Fin.ext
    have packed := mean x n j h g
    rw [vacant] at packed
    exact packed

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
