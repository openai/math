import OAI.Hierarchy.DescentOrdinaryDatedEntry
import OAI.Hierarchy.DescentIssuedOrdinaryResult
import OAI.Hierarchy.DescentDatedPublicOrdinaryCode

namespace OAI
/-! # The ordinary step on a public calendar and its actual preceding registers -/
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

def ordinaryModel : PhysicalOrdinary F P := (base).registeredFrom prior floor

local notation "v" => ordinaryModel prior ticket op gain tail p f drift degree payload seats root ordinary

def ordinaryPorts : DatePorts := DatePorts.ordinary (v) floor

theorem ordinary_arguments : (v).vector.operands=max prior.argumentsPerNode (S.retainedArgumentsAt G drift) :=rfl

local notation "A" => (base).registeredEntry prior floor
local notation "match₀" => (base).registered_match prior floor (Nat.le_max_left prior.argumentsPerNode (S.retainedArgumentsAt G drift))
local notation "sh" => (base).registered_geometry prior floor
local notation "B" => (v).reachedSources floor

/-- The room demanded by the existing native phases, on the actual banks
selected from the preceding date. No field selects instructions or input data. -/
structure OrdinaryCodeRoom (w : ℕ) : Prop where
  signed : (v).SignedChart
  blocks : (v).resolver.blocks=(v).material.blocks
  paths : (A).clip.venue.paths=StageVenueTail.OrdinaryRaster.paths (v).area
  slots : 0<(v).vector.operands
  chip : ((A).chipBank (v) floor).Fits w ((v).refsStart floor)
  endFit : (v).endAddress floor<2^w
  packed : (v).resolver.lanes*DescentPackedOperand.unit (v).resolver.size≤w/2
  radix : (v).vector.radix=2^(v).reference.k
  funded : (v).FundedRoom floor ((v).fundedFromEntry floor (A) paths) prior.io w
  result : (v).ResultRoom floor (B) w

variable (w : ℕ) (shelf header : ℕ) (pos : 0<k)
variable (room : OrdinaryCodeRoom prior ticket op gain tail p f drift degree payload seats root ordinary w)
local notation "steps" => (v).issuedSteps root prior (A) room.signed w (match₀) (sh) room.blocks room.paths
  room.slots room.chip room.endFit room.packed room.radix room.funded

/-- The physical profile load, matcher, donor, signed/operand return and counter
all read addresses from this one registered ordinary cut. -/
def ordinaryDate : DateCode w :=
  (v).date root shelf header prior.io prior.archive.count ((v).signedInput floor room.signed) (B)
    (steps) room.result (DonorDate.atDate G S gain k i p) pos

theorem ordinary_room_irrel
    (other : OrdinaryCodeRoom prior ticket op gain tail p f drift degree payload seats root ordinary w) :
    ordinaryDate prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room =
      ordinaryDate prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos other :=rfl

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
