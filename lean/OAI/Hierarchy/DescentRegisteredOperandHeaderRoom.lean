import OAI.Hierarchy.DescentDatedRetainedHeaderFrame
import OAI.Hierarchy.DescentDatedTicketPreparationTotal
import OAI.Hierarchy.DescentRegisteredArgumentGatherRoom
import OAI.Hierarchy.DescentOrdinaryPreparedLimit

namespace OAI
/-! # The registered ticket admission covers every original retained header bank -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup ProtocolRAM
open DescentRawCablePanel Computability.VPVNP.BurstRAM PrivateRAM
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


open DescentDatedSourcePathDirectory DescentHaloWalkRAM DescentPacking.PackedMatch.Local.Stage.Chooser
local notation "refs₀" => ((A).directory (v) floor (match₀)).refs
local notation "e₀" => (v).material
local notation "fmt₀" => (v).ticket.depotShape (v).short
local notation "pa" => (v).operandPathStart floor
local notation "rk" => (v).operandRankStart floor

theorem registered_operand_header_room {w : ℕ} (chart : (v).SignedChart) (pg : Fin (7*(v).vector.operands))
    (inlet : (A).Room (v) floor w) (previous : prior.venue.groups=S.groupCount i)
    (admission : (v).TicketAdmission floor w chart (A) (match₀) pg) (endFit : (v).endAddress floor<2^w) :
    (v).OperandHeaderRoom floor (A) (match₀) refs₀ (refs₀ pg) w :=by
  have allFit:=((base).registered_prepared_limit prior floor).trans_lt endFit
  obtain ⟨r₁,r₂,r₃,r₄,r₅,r₆,r₇,r₈,r₉⟩:=(v).ticket_source_order floor
  have headFit:=r₇.trans_lt (r₈.trans_lt (r₉.trans_lt allFit))
  have routeFit:=r₁.trans_lt (r₂.trans_lt (r₃.trans_lt (r₄.trans_lt (r₅.trans_lt (r₆.trans_lt headFit)))))
  have gathered:=ordinary_gather_room prior ticket op gain tail p f drift degree payload seats root ordinary
    inlet previous admission.lanes routeFit
  have span : pa+(e₀).oldHosts≤rk:=
    paths_fit_hosts (e₀).oldHosts (e₀).groups (e₀).lanes (fmt₀).degree pa
  have first : pa≤rk:=(Nat.le_add_right ..).trans span
  have next : rk≤(v).operandOldHeaderStart floor:=Nat.le_add_right ..
  obtain ⟨paths,ep,local_⟩:=native_header_room (e₀).oldHosts (e₀).groups (e₀).lanes (fmt₀).degree
    ((v).donorEnd floor) pa w admission.prior (span.trans_lt (next.trans_lt (r₅.trans_lt (r₆.trans_lt headFit))))
  exact ⟨inlet,gathered,admission.mask,admission.groups,admission.refs,admission.panel,admission.capacity,
    admission.bits,paths,bank_before ep first,bank_before local_ first,headFit⟩

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
