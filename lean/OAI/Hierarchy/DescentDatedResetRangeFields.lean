import OAI.Hierarchy.DescentResetPostedRange
import OAI.Hierarchy.DescentTerminalResetDatedFields

namespace OAI
/-! # The three actual retained range pages after a scheduled reset -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentOperandCandidateLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "A" => (v).receiver
local notation "s" => u.operand
local notation "start" => (v).sheetsStart b
local notation "plan" => (v).linkedRankInputs u.sectors start
local notation "rendered" => (v).renderFromRanks plan b
local notation "actorBase" => (v).middle.stop b
local notation "head" => a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "ht" => a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits

variable {u} (z : u.FinalInputs)
theorem dated_span_fields (ok : u.Ready) (room : z.Room) {m mid dst : Memory w}
    (earlier : u.throughOperandDate.Runs m mid) (run : (date z).Runs m dst)
    (bits : (s).coeff=(v).nodeBits) :
    ∃actorMem,((head).seq ((v).actor.actorBody u.actor actorBase w)).Exec m actorMem
        (ht+(v).actor.actorTicks u.actor actorBase w) ∧
      ∀(f:Fin 3) (arg:Fin (v).argumentSlots) (x:Fin (A).blocks)
       (kept : Fin (v).nodes→Fin (A).hosts→Fin (A).groups→Cell (s).coeff),
       (∀n,Source ((s).kept ((v).operandOrdinal (s) (DescentRetainedRangeDigits.page f) (arg.cast ok.slots.symm) x (n.cast ok.nodes.symm)))
         (kept n) (A).lanes (u.operandEntry ok actorMem)) →
       Reads ((v).terminalField b (DescentRetainedRangeDigits.page f) arg x) (fun h g=>encode (v).nodeBits (v).nodes
         (fun n=>(kept n h g).cast (congrArg (2^·) bits))) (A).lanes dst := by
  obtain ⟨actorMem,acted,equal⟩:=u.sheets_result ok earlier
  refine ⟨actorMem,acted,?_⟩
  intro f arg x kept old
  apply terminal_operand z room earlier run (DescentRetainedRangeDigits.page f) arg x
  rw [equal]
  exact (v).span_field_posted plan (s) b u.degree u.bank u.laws (u.candidateEntry ok actorMem)
    ok.nodes ok.slots bits ok.fields ok.full f arg x kept old

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
