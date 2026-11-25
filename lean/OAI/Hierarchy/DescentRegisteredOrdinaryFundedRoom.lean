import OAI.Hierarchy.DescentDatedFundedCompactRoom
import OAI.Hierarchy.DescentRegisteredOrdinaryStep

namespace OAI
/-! # The calendar issuer supplies the funded room of the literal ordinary CPU -/
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

local notation "v" => ordinaryModel prior ticket op gain tail p f drift degree payload seats root ordinary

local notation "entry" => (base).registeredEntry prior floor

/-- On an ordinary calendar entry, the old group count is exactly one radix
times the next group count. The maximum address includes both compact rasters. -/
theorem ordinary_funded_room {w : ℕ} (age : i<S.length) (radix : S.radix=2^k)
    (paths : (entry).clip.venue.paths=StageVenueTail.OrdinaryRaster.paths (v).area)
    (inlet : (entry).Room (v) floor w) (previous : prior.PaidRoom w root)
    (positive : 0<(v).resolver.lanes) (space : (v).fullEnd root<2^w) :
    (v).FundedRoom floor ((v).fundedFromEntry floor (entry) paths) prior.io w := by
  have split : (base).venue.groups*2^(base).area.k=(base).area.G:=by
    change S.groupCount (i+1)*2^k=S.groupCount i
    have rest : S.length-i=(S.length-(i+1))+1:=by omega
    change (S.baseGroups*S.radix^(S.length-(i+1)))*2^k=S.baseGroups*S.radix^(S.length-i)
    rw [rest,pow_succ,←radix,Nat.mul_assoc]
  have earlier : root≤floor:=by
    change root≤(base).profileRepack.endAddress root
    rw [(base).profileRepack.translate]
    exact Nat.le_add_right ..
  have past : (v).rasterEnd floor≤(v).fullEnd root:=(v).raster_below_full root
  exact (base).registered_funded_room prior floor (Nat.le_max_left prior.argumentsPerNode (S.retainedArgumentsAt G drift))
    paths inlet (previous.mono earlier) split positive (past.trans_lt space)

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
