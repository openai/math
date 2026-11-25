import OAI.Hierarchy.DescentOrdinaryResultRoom
import OAI.Hierarchy.DescentRegisteredOrdinaryVenueRoom

namespace OAI
/-! # The registered ordinary result fits at its published upper address -/
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

theorem ordinary_result_room {w : ℕ} (limit : (v).operandEnd floor<2^w) :
    (v).ResultRoom floor ((v).reachedSources floor) w := by
  have inputs : (v).metaStart floor≤(v).metaEnd floor:=by
    rw [PhysicalOrdinary.metaEnd,(v).metadata.ordinary_translate];exact Nat.le_add_right ..
  have outputs : (v).metaEnd floor≤(v).operandEnd floor:=by
    rw [PhysicalOrdinary.operandEnd,(v).operandBook.affine];exact Nat.le_add_right ..
  have geometry:=(base).registered_node_chart prior floor
  exact (v).result_room floor _ ((base).registered_geometry prior floor) geometry.1 rfl geometry.2
    (ordinary_model_venue_room prior ticket op gain tail p f drift degree payload seats root ordinary w
      (inputs.trans_lt (outputs.trans_lt limit))) limit

theorem ordinary_header_dimensions (age : i<S.length) (radix : S.radix=2^k) :
    (v).vector.bookBits=((v).resolver.size+2)*(v).resolver.nodes ∧
    (v).bornBook.hosts=(v).vector.hosts ∧
    (v).bornBook.lanes=(v).vector.lanes*(v).vector.radix ∧
    (v).bornBook.groups=(v).vector.groups*(v).vector.radix := by
  refine ⟨rfl,rfl,rfl,?_⟩
  change S.groupCount i=S.groupCount (i+1)*2^k
  simpa only [Fintype.card_fin,Fintype.card_prod] using Fintype.card_congr (S.groupDigits age radix)

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
