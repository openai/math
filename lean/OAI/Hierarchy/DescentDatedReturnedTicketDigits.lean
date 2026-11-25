import OAI.Hierarchy.DescentDatedSampledOperandValues
import OAI.Hierarchy.DescentDatedOperandPhysicalRead
import OAI.Hierarchy.DescentDatedNativeTicketRead

namespace OAI
/-! # Original signed and private operands through the complete mixed-width ticket return -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentSIMDLookup DescentPackedZip
open DescentRawCablePanel DescentHaloWalkRAM DescentSharedCableNames ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
set_option hygiene false
set_option quotPrecheck false
local notation "e" => v.material
local notation "fmt" => v.ticket.depotShape v.short
local notation "P" => breadth (fmt).degree
local notation "O" => DepotRAM.Material.roles fmt
local notation "l" => v.resolver
local notation "g" => v.ticketReadGeometry
local notation "J" => (l).jobs
local notation "d" => v.operandShortBits
local notation "b" => (e).fieldBits
local notation "pwidth" => Packed.bits P

variable (floor : ℕ) (c : v.SignedChart) (A : v.ArgumentEntry) (matched : A.Match v floor)
    (shape : v.VectorShape) (blocks : (l).blocks=(e).blocks)
local notation "heads" => v.nativeTicketSources floor c A matched shape blocks
variable (data : v.OriginalData)
variable {w : ℕ} (m : Memory w)
local notation "castStage" => DescentDatedOperandCasts.phase v.operandWidth d (l).lanes (v.headTransferEnd floor) w
local notation "pre" => v.headTransferEnd floor
local notation "start" => v.operandRootBase floor
set_option hygiene true
set_option quotPrecheck true
open DescentDatedOperandCoordinates.Ticket
theorem returned_ticket_digits (reach : Fin (e).oldHosts→Fin P→Option (Fin (e).oldHosts))
    (rosters : v.WalkBanks floor A reach pre m) (old : v.OriginalReads floor A matched shape blocks data m)
    (space : v.preparedUntil floor < 2^w) (lanes : 0 < (g).lanes) (width : (g).resultBits*(g).lanes ≤ w) :
    let program:=(castStage).seq (v.sortedTicketPhase floor w c A matched shape blocks)
    Step pre (v.preparedUntil floor) program m ∧ ∀job h k f,
      socketDigit (g).resultBits (g).lanes (v.nativeTicketExpr floor c A matched shape blocks job f) (program.image m) h k=
        ((ticketAt g (SortedInput.values g (v.originalValues data) (v.walkValues reach)) job h k f:ℕ):Cell (g).resultBits).val :=by
  intro program
  obtain ⟨run,fieldReads⟩:=v.native_source_returns floor c A matched shape blocks data m reach rosters old space
  refine ⟨run,?_⟩
  intro job h k f
  have read:=socket_digit _ (program.image m) _ (fieldReads job f).read lanes width h k
  exact read.trans (congrArg Fin.val (final_ticket g (SortedInput.values g (v.originalValues data) (v.walkValues reach)) job h k f))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
