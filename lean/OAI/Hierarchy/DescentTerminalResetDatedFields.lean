import OAI.Hierarchy.DescentTerminalResetOperandRead
import OAI.Hierarchy.DescentTerminalResetRoleArity

namespace OAI
/-! # All seven retained operand fields in the actual dated output -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentOperandCandidateLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
open scoped Fin.CommRing
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

def DateInputs.candidateEntry (ok : u.Ready) (actorMem : Memory w) :=
  DescentResetCandidatePair.memory start u.sectors.pageBits (A).hosts (A).groups (A).lanes
    u.sectors.header u.sectors.original (u.sheetsEntry ok actorMem)

def DateInputs.operandEntry (ok : u.Ready) (actorMem : Memory w) :=
  (v).terminalQueryMemory plan b u.degree u.bank u.laws (u.candidateEntry ok actorMem)

variable {u} (z : u.FinalInputs)
theorem dated_fields (ok : u.Ready) (room : z.Room) {m mid dst : Memory w}
    («prefix» : u.throughOperandDate.Runs m mid) (run : (date z).Runs m dst)
    (bits : (s).coeff=(v).nodeBits) (small : 2*(A).candidates<2^(A).queryBits) :
    ∃actorMem,((head).seq ((v).actor.actorBody u.actor actorBase w)).Exec m actorMem
        (ht+(v).actor.actorTicks u.actor actorBase w) ∧
      ∀(q : Fin (A).fields→Fin (A).hosts→Fin (A).groups→Option (Fin (2*(A).candidates)))
       (raw : Fin (A).fields→Fin (2*(A).candidates)→Fin (A).hosts→Fin (A).groups→Cell (A).signedBits)
       (kept value : Fin (A).fields→Fin (A).hosts→Fin (A).groups→Cell (s).coeff),
       (∀i,Source ((s).query i) (fun h g=>code small (q i h g)) (A).lanes (u.operandEntry ok actorMem)) →
       (∀i,Source ((s).kept i) (kept i) (A).lanes (u.operandEntry ok actorMem)) →
       (∀i j,Source ((v).previous (s) rendered b i j) (raw i j) (A).lanes (u.operandEntry ok actorMem)) →
       (∀i h g,(kept i h g).val+
        (selected (q i) (fun j h g=>((raw i j h g).val:Cell (s).coeff)) h g).val=(value i h g).val) →
       ∀(f:Fin 7) (arg:Fin (v).argumentSlots) (x:Fin (A).blocks),
       Reads ((v).terminalField b f arg x) (fun h g=>encode (v).nodeBits (v).nodes (fun n=>
         (value ((v).operandOrdinal (s) f (arg.cast ok.slots.symm) x (n.cast ok.nodes.symm)) h g).cast (congrArg (2^·) bits)))
         (A).lanes dst := by
  obtain ⟨actorMem,acted,equal⟩:=u.sheets_result ok «prefix»
  refine ⟨actorMem,acted,?_⟩
  intro q raw kept value issued previous fresh coeff f arg x
  apply terminal_operand z room «prefix» run f arg x
  rw [equal]
  exact (v).terminal_field_posted plan (s) b u.degree u.bank u.laws (u.candidateEntry ok actorMem)
    ok.nodes ok.slots bits ok.fields ok.full small q raw kept value issued previous fresh coeff f arg x

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
