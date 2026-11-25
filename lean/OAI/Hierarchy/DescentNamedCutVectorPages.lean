import OAI.Hierarchy.DescentNamedCutResolverMemory
import OAI.Hierarchy.DescentDatedPreviousPagesBeforeWrite
import OAI.Hierarchy.DescentDatedRegisteredPointerRows
import OAI.Hierarchy.DescentRegisteredOrdinaryMemories

namespace OAI
/-! The genuine registered scalar vector books at a chronological cut. -/
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
local notation:max "donors" m:arg => ordinaryDonorMemory prior ticket op gain tail p f drift degree payload seats root ordinary
  w shelf header pos room exec m
open DescentDatedPriorOperand DescentPackedColony
local notation "E₀" => (A).samePorts (phys)
local notation:max "signed₀" m:arg => ((v).signedReturn floor prior.io prior.archive.count (steps).parts (steps).adjacency w).image (donors m)
local notation:max "actual₀" m:arg => ordinaryMetadata prior ticket op gain tail p f drift degree payload seats root ordinary
  w shelf header pos room exec m


open DescentHaloWalkRAM DescentOperandVectorArena DescentOrdinaryAtomFieldRAM DescentPackedColony
open DescentDatedPriorOperand DescentOrdinaryReferenceInputs
local notation "signedMem" m:arg => ordinarySignedMemory prior ticket op gain tail p f drift degree payload seats root ordinary
  w shelf header pos room exec m


set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
/-- The seven books of the actual W on the metadata writer's state. The ticket
directory keeps them below its first write in every preparation phase. -/
theorem registered_vector_pages_at_metadata {nb mb : ℕ} (m : Memory w)
    (admit : (v).TicketAdmission floor w room.signed (A) (match₀) pg)
    (bits_ : (v).vector.bookBits=((v).resolver.size+2)*(v).resolver.nodes)
    (V : References.Rows (v).vector (v).reference.degree (v).reference.k (v).reference.oldNodes
      (v).reference.capacity ((v).resolver.size+2) nb mb)
    (native : ∀(page : Fin (v).vector.pageCount) (rowIndex : Fin (v).vector.lows),
      ScalarOperand.Measured (((A).directory (v) floor (match₀)).refs page rowIndex) (V page rowIndex)
      (v).resolver.nodes ((v).vector.lanes*(v).vector.radix) ((v).vectorStart floor)
      ((A).mountedTape (v) floor (signedMem m))) :
    ∀x col,Reads (previousBank (v).resolver ((v).vectorOutput floor) x col)
      (((v).registeredOperandBooks (sh) V) x col) (v).resolver.lanes (actual₀ m) :=by
  have extent : (v).origin.grainBase ((v).routedStart floor)=(v).preparedUntil floor:=by
    apply (v).grain_after_sources
    exact ((base).fundedFrom prior floor).origin_reservation
  have low : (v).preparedUntil floor≤(v).origin.outputBase ((v).routedStart floor):=by
    rw [←extent]
    exact Nat.le_add_right ..
  have endFit : (v).preparedUntil floor<2^w:=by
    have above : (v).origin.outputBase ((v).routedStart floor)≤(v).normalizedEnd floor:=by
      change _≤(v).origin.endAddress ((v).routedStart floor)
      rw [(v).origin.affine]
      exact Nat.le_add_right ..
    exact (low.trans (above.trans ((v).resolver.floor_le _))).trans_lt room.endFit
  have prepared:=(v).ticket_preparation_any floor w room.signed (A) (match₀) (sh) room.blocks pg admit endFit
  have source:=fun j f=>ProtocolRAMGeneratedWrite.fits_mono _ low ((prepared (fun _=>0)).2 j f)
  have data:=(v).previous_pages_before_write root shelf header prior.io prior.archive.count digits (B)
    steps room.result date₀ pos exec (A) (match₀) _ _ room.chip (sh) room.endFit room.packed rfl
    source (fun mem a early=>(prepared mem).1.frame a (.inl early))
    V bits_ admit.lanes admit.radix m native
  exact fun x col=>data col x

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
