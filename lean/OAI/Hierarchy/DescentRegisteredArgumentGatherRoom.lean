import OAI.Hierarchy.DescentRegisteredOrdinaryStep
import OAI.Hierarchy.DescentOrdinaryArgumentInletRoom

namespace OAI
/-! The original argument-gather room on the registered ordinary calendar. -/
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

theorem ordinary_gather_room {w : ℕ} (inlet : (A).Room (v) floor w)
    (previous : prior.venue.groups=S.groupCount i)
    (lanes : 0 < (v).vector.lanes) (limit : (v).routedStart floor<2^w) :
    ((A).directory (v) floor (match₀)).refs.Room w ((v).vectorStart floor) :=by
  exact (A).gather_room (v) floor (match₀) inlet previous.symm rfl rfl rfl (Nat.two_pow_pos k) lanes limit

/-- The original donor word and the projected birth word are both priced in the
same public table of sixteen actual ordinary input widths. -/
theorem ordinary_inlet_chip
    (format : (A).clip.venue.socket=(DonorDate.atDate G S gain k i p).format)
    (w : ℕ) (word : payload≤w) :
    (A).clip.working*max (DepotRAM.totalBits (A).clip.venue.socket)
      (DepotRAM.outputBits (A).clip.venue.socket)≤w/2 :=by
  have paid:=((base).registered_width prior floor).1
  have raw : DepotRAM.totalBits (A).clip.venue.socket*(A).clip.working≤payload/4:=paid 3
  have born : ((v).bornBook.chipBits*1+(v).bornBook.chipBits)*(A).clip.working≤payload/4:=paid 6
  have projected : DepotRAM.outputBits (A).clip.venue.socket=(v).bornBook.chipBits:=by
    rw [format]
    rfl
  rw [Nat.mul_comm,projected,max_mul]
  apply max_le
  · omega
  · have le_ : (v).bornBook.chipBits≤(v).bornBook.chipBits*1+(v).bornBook.chipBits:=Nat.le_add_left ..
    have scaled:=Nat.mul_le_mul_right (A).clip.working le_
    omega

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
