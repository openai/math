import OAI.Hierarchy.DescentReturnedMetadataPaid
import OAI.Hierarchy.DescentRegisterArchiveFlagAfter

namespace OAI
/-! The ordinary metadata rows at genuine named archive positions, including unpaid nodes. -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 1500000
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

private theorem natFlagCell {bits : ℕ} (test : Prop) [Decidable test] :
    ((if test then 1 else 0 : ℕ) : Cell bits) = (if test then 1 else 0 : Cell bits) := by
  split <;> rfl

private theorem transferEncoded {H C a n b lanes : ℕ} {page : Bank} {mem : Memory b}
    {left right : Fin H → Fin C → Fin n → Cell a} (agree : ∀ h g j, left h g j = right h g j)
    (read : Reads page (fun h g => encode a n (left h g)) lanes mem) :
    Reads page (fun h g => encode a n (right h g)) lanes mem := by
  have eqn : left = right := funext fun h => funext fun g => funext fun j => agree h g j
  exact eqn ▸ read

private theorem naturalLengthCell {α : Type*} {b : ℕ} (choice : Option α) (length : α → ℕ) :
    ((choice.elim 0 length : ℕ) : Cell b) = choice.elim 0 (fun x => (length x : Cell b)) := by
  cases choice <;> rfl

omit [Fintype P] in
theorem returned_archive_metadata (m : Memory w) (wide : Fintype.card next.V≤(v).venue.hosts)
    (crop : (v).resolver.hosts≤(v).venue.hosts)
    (issued : returnedVenue prior ticket op gain tail p f drift degree payload seats root ordinary
      w shelf header pos room exec m)
    (words : Fin (chart).blocks→Fin (v).resolver.operands→Fin (chart).hosts→Fin (chart).groups→Cell ((sb)*(chart).nodes))
    (printed : ∀x j,Reads (spans x j) (words x j) (chart).lanes (record m))
    (bounded : ∀x n h g,lengthAt x n h g ≤ (v).resolver.operands)
    (live : ∀x n j h g,DescentOrdinaryAtomFieldRAM.ScalarOperand.take (a:=sb) n (words x j h g)≠0 ↔
      j.val<lengthAt x n h g)
    (mass : next.placement.wire*(next.placement.z*G.b)*next.placement.cap<2^(S.censusBits p)) :
    (∀x,Reads (metadataPage ports 0 x) (fun h g=>encode (ports).operandBits (ports).nodes
      (fun j=>(flag x j h g : Cell (ports).operandBits))) (ports).operandLanes (record m)) ∧
    ∀x,Reads (metadataPage ports 1 x) (fun h g=>encode (ports).operandBits (ports).nodes
      (fun j=>(lengthAt x j h g : Cell (ports).operandBits))) (ports).operandLanes (record m) := by
  let length := fun x n h g => lengthAt x n h g
  have pair := returned_metadata_rows prior ticket op gain tail p f drift degree payload seats root ordinary
    w shelf header pos room exec m wide crop issued words printed length bounded live
  constructor
  · intro x
    have value (h : Fin (v).resolver.hosts) (g : Fin (v).resolver.groups) (j : Fin (v).resolver.nodes) :
        (flag x j h g : Cell (ports).operandBits) =
        (if j.val<(Census.count next.placement (Equiv.refl _) (next.vertex.trans (Fin.castLEEmb wide))
          pb (h.castLE crop) g x).val then 1 else 0) := by
      have natural := RegisterTimeline.archiveFlag_after next (Nat.succ_pos _) desc ord ports places wide
        (S.censusBits p) mass x j h g (h.castLE crop) rfl
      change flag x j h g = if j.val < (Census.count next.placement (Equiv.refl _)
        (next.vertex.trans (Fin.castLEEmb wide)) pb (h.castLE crop) g x).val then 1 else 0 at natural
      exact (congrArg (fun y : ℕ => (y : Cell (ports).operandBits)) natural).trans (natFlagCell _)
    refine transferEncoded (left:=fun h g j => if j.val < (Census.count next.placement (Equiv.refl _)
      (next.vertex.trans (Fin.castLEEmb wide)) pb (h.castLE crop) g x).val then 1 else 0)
      (right:=fun h g j => (flag x j h g : Cell (chart).bits)) ?_ ?_
    · exact fun h g j => (value h g j).symm
    · have result := pair 0 x
      simp only [↓reduceIte] at result
      exact result
  · intro x
    refine transferEncoded (left:=fun h g j => (length x j h g : Cell (chart).bits))
      (right:=fun h g j => (lengthAt x j h g : Cell (ports).operandBits)) ?_ ?_
    · exact fun h g j => naturalLengthCell (atNode x j h g) _
    · have result := pair 1 x
      simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte] at result
      exact result

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
