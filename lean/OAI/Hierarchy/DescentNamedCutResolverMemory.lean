import OAI.Hierarchy.DescentDatedResolverWordFrame
import OAI.Hierarchy.DescentRegisteredSignedMemory
import OAI.Hierarchy.DescentDatedOrdinaryRegisteredOperand

namespace OAI
/-! The observed physical resolver words on the original ordinary date's argument writer. -/
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
local notation "pg" => (⟨0,Nat.mul_pos (by decide : 0<7) room.slots⟩:Fin (7*(v).vector.operands))

variable (exec:OrdinaryExecutionRoom prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header room)
local notation "phys" => (v).withIssuedSigned
local notation "donors" m => ordinaryDonorMemory prior ticket op gain tail p f drift degree payload seats root ordinary
  w shelf header pos room exec m
open DescentDatedPriorOperand DescentPackedColony
local notation "E₀" => (A).samePorts (phys)
local notation "signed₀" m => ((v).signedReturn floor prior.io prior.archive.count (steps).parts (steps).adjacency w).image (donors m)
local notation "actual₀" m => ordinaryMetadata prior ticket op gain tail p f drift degree payload seats root ordinary
  w shelf header pos room exec m

set_option maxRecDepth 4096 in
/-- The output of the selected physical signed model, on its actual mounted tape, at
the consecutive metadata and argument writers of the original ticket. The cell family
is preserved literally, including every decoded operand and its padding lanes. -/
theorem normalized_keys_on_date (m : Memory w) (fixed : phys=v)
    (mt : (E₀).Match phys floor) (shape : (phys).VectorShape)
    (blocks : (phys).resolver.blocks=(phys).material.blocks)
    (limit : (phys).endAddress floor<2^w)
    (wide : (phys).resolver.lanes*DescentPackedOperand.unit (phys).resolver.size≤w/2)
    {a : ℕ} (values : Fin (v).resolver.jobs→Fin (v).resolver.hosts→Fin (v).resolver.groups→Cell a)
    (keys : ∀j,Reads (Banks.wordBank (phys).resolver ((phys).normalizedEnd floor) j) (values j)
      (phys).resolver.lanes
      (((phys).routedArguments floor ((E₀).directory (phys) floor mt).refs
        ((phys).nativeTicketExpr floor (v).issuedSignedChart (E₀) mt shape blocks)
        ((phys).nativeTicketPreparation floor w (v).issuedSignedChart (E₀) mt shape blocks pg)
        shape limit wide).image ((E₀).mountedTape (phys) floor (signed₀ m)))) :
    ∀j,Reads (Banks.wordBank (v).resolver ((v).normalizedEnd floor) j) (values j)
      (v).resolver.lanes (actual₀ m) :=by
  have selected:=ordinary_signed_image prior ticket op gain tail p f drift degree payload seats root ordinary
    w shelf header pos room exec m fixed
  have joined:=PhysicalOrdinary.mounted_resolver_image fixed floor w (A) room.signed (v).issuedSignedChart
    (match₀) mt (sh) shape room.blocks blocks room.slots room.slots room.endFit limit room.packed wide _ _ selected
  have address:=congrArg (fun (model:PhysicalOrdinary F P)=>model.normalizedEnd floor) fixed
  apply (v).resolver_words_before_write root shelf header prior.io prior.archive.count digits (B) steps
    room.result date₀ pos exec m values
  intro j
  have same := congrArg₂ (fun (atEnd : ℕ) (memory : Memory w) =>
    Reads (Banks.wordBank (v).resolver atEnd j) (values j) (v).resolver.lanes memory) address joined
  exact same.mp (keys j)

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
