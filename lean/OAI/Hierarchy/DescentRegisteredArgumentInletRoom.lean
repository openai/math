import OAI.Hierarchy.DescentRegisteredArgumentGatherRoom
import OAI.Hierarchy.DescentDatedArgumentRegisters
import OAI.Hierarchy.DescentInitialRolePages

namespace OAI
/-! # The paid ordinary inlet uses the actual seven and primitive archives from the previous date -/
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

theorem ordinary_inlet_room {w : ℕ}
    (venue : (A).clip.Room (A).venue ((v).signedEnd floor) w)
    (old : prior.argumentLimit (2^k)≤(v).signedEnd floor)
    (roles : prior.archive.roles.endAddress≤(v).signedEnd floor) (blocks : 2^k≤prior.archive.roles.blocks)
    (format : (A).clip.venue.socket=(DonorDate.atDate G S gain k i p).format)
    (word : payload≤w) (limit : (v).refsStart floor<2^w) :
    (A).Room (v) floor w := by
  have cut : (v).signedEnd floor<2^w:=(show (v).signedEnd floor≤(v).refsStart floor from Nat.le_add_right ..).trans_lt limit
  exact (A).inlet_room (v) floor venue
    (prior.prior_fits (2^k) _ w old cut)
    (fun x=>prior.archive.roles.fits w _ x.val (x.isLt.trans_le blocks) roles cut)
    (ordinary_inlet_chip prior ticket op gain tail p f drift degree payload seats root ordinary format w word)
    ((match₀).atRefs.trans_lt limit)

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
