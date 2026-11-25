import OAI.Hierarchy.DescentDatedRegisteredHeaders
import OAI.Hierarchy.DescentRegisteredOrdinaryResultRoom

namespace OAI
/-! # Measured native header fields on the physically registered ordinary date -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentOrdinaryOriginMask
open DescentPacking.PackedMatch.Local.Stage DescentRawCablePanel ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
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

local notation "v" => ordinaryModel prior ticket op gain tail p f drift degree payload seats root ordinary

local notation "A" => (base).registeredEntry prior floor
local notation "match₀" => (base).registered_match prior floor (Nat.le_max_left prior.argumentsPerNode (S.retainedArgumentsAt G drift))
local notation "sh" => (base).registered_geometry prior floor

local notation "rc₀" => (v).resolver
local notation "vx₀" => (v).vector
local notation "bn₀" => (v).bornBook
local notation "g₀" => (v).ticketReadGeometry
local notation "M₀" => (rc₀).lanes
local notation "W₀" => (vx₀).lanes*(vx₀).radix
local notation "vecAt" => (v).vectorStart floor
local notation "mouthEnd₀" => (v).originMouthEnd floor
local notation "headerEnd" => (v).operandHeaderEnd floor
local notation "e₀" => (v).material
local notation "fmt₀" => (v).ticket.depotShape (v).short
local notation "ps₀" => (v).operandPathStart floor
local notation "refs₀" => ((A).directory (v) floor (match₀)).refs
local notation "Val₀" => References.Rows (v).vector (v).reference.degree (v).reference.k (v).reference.oldNodes
  (v).reference.capacity ((rc₀).size+2)
local notation "dims₀" => ordinary_header_dimensions prior ticket op gain tail p f drift degree payload seats root ordinary
theorem ordinary_booked_headers {w nb mb} (age : i<S.length) (radix : S.radix=2^k) (pg : Fin (vx₀).pageCount)
    (chip : Fin (bn₀).hosts→Fin (bn₀).groups→Cell (bn₀).chipBits)
    (oldBooks : Val₀ nb mb)
    (m : Memory w) (good : (refs₀).Room w vecAt)
    (input : ((A).chipBank (v) floor).Fits w vecAt) (span : (bn₀).rows≤((A).chipBank (v) floor).size)
    (read : Reads ((A).chipBank (v) floor) chip (bn₀).lanes m)
    (pages : ∀p q,Measured ((refs₀) p q) (oldBooks p q) (rc₀).nodes W₀ vecAt m)
    (panelLow : (A).venue.panel.base+(A).venue.panel.size≤ mouthEnd₀)
    (panelSize : (e₀).oldHosts*chunks (e₀).oldGroups (e₀).oldLanes≤(A).venue.panel.size)
    (panelWord : (e₀).oldLanes*max (DepotRAM.totalBits fmt₀) (e₀).fieldBits≤w/2)
    (earlier : PriorHeader.endAddress (e₀).oldHosts (e₀).groups (e₀).lanes (fmt₀).degree ((v).donorEnd floor)≤ps₀)
    (space : headerEnd<2^w) :
    let dims:=dims₀ age radix
    let home:=dims.2.1
    let group:=dims.2.2.2
    let word : (bn₀).bits=(rc₀).size+2:=rfl
    let mouthRows:=(v).headerMouthRows floor (A) (match₀) oldBooks home group word
    let first:=((refs₀).phase w vecAt).image m
    let here:=((v).originAndMouth floor w (A) (match₀) (v).operandShortBits ((refs₀) pg)).image first
    let last:=((v).operandEarlyPhase floor w A).image here
    (∀j f,Held g₀ headerEnd last ((v).originAt floor (v).operandShortBits (sh) j f) ((v).originHeaderValue (sh) (oldBooks pg) j f)) ∧
    (∀j f,Held g₀ headerEnd last ((v).oldHeaderAt floor j f)
      (fun h k=>ScalarOperand.take (((rc₀).index.symm j).2.1) ((v).previousHeaderValue (sh) oldBooks j f h k))) ∧
    ∀j f,Held g₀ headerEnd last ((v).mouthAt floor (A) (match₀) (sh) j f)
      (fun h k=>ScalarOperand.take (((rc₀).index.symm j).2.1) ((v).mouthHeaderValue floor (A) (match₀) (sh) mouthRows chip home group j f h k)) :=by
  obtain ⟨wide,home,lane,group⟩:=dims₀ age radix
  exact (v).registered_headers floor (A) (match₀) (sh) pg chip oldBooks m good input span read home lane group rfl wide
    pages panelLow panelSize panelWord earlier space

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
