import OAI.Hierarchy.DescentReturnedPackedMetadata
import OAI.Hierarchy.DescentNamedCutVectorPages

namespace OAI
/-! All ordinary operand writer inputs on the same registered metadata memory. -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
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

open DescentDatedPriorOperand DescentOperandStateBanks

theorem returned_writer_rows (m : Memory w) (wide : Fintype.card next.V≤(v).venue.hosts)
    (crop : (v).resolver.hosts≤(v).venue.hosts)
    (funded_ : returnedVenue prior ticket op gain tail p f drift degree payload seats root ordinary
      w shelf header pos room exec m)
    (old : Books (v).resolver) (jobs : Fin (v).resolver.jobs→DescentDatedPriorOperand.Source (v).resolver)
    (printed : ∀x pg,Reads (previousBank (v).resolver ((v).vectorOutput floor) x pg) (old x pg)
        (v).resolver.lanes (record m))
    (normalized : ∀j,Reads (Banks.wordBank (v).resolver ((v).normalizedEnd floor) j)
      (fun h g=>DescentPackedOperand.word ((jobs j).compiled h g)) (v).resolver.lanes (record m)) :
    ∃(metadataRows : (v).MetaWords) (bks : Books (v).resolver)
      (src : Fin (v).resolver.jobs→DescentDatedPriorOperand.Source (v).resolver),
      (∀f x,Reads ((v).nodeChart.bank ((v).nodeBankBase floor) f x) (metadataRows f x)
        (v).resolver.lanes (record m)) ∧
      (∀x pg,Reads (previousBank (v).resolver ((v).vectorOutput floor) x pg) (bks x pg)
        (v).resolver.lanes (record m)) ∧
      ∀j,Reads (Banks.wordBank (v).resolver ((v).normalizedEnd floor) j)
        (fun h g=>DescentPackedOperand.word ((src j).compiled h g)) (v).resolver.lanes (record m) :=by
  obtain ⟨metadataRows,read⟩:=returned_metadata_packed prior ticket op gain tail p f drift degree payload seats root ordinary
    w shelf header pos room exec m wide crop funded_ (fun x j=>old x (page 6 j)) (fun x j=>printed x (page 6 j))
  exact ⟨metadataRows,old,jobs,read,printed,normalized⟩

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
