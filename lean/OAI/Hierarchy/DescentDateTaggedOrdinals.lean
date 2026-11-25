import OAI.Hierarchy.DescentResetRegisteredOperandRows

namespace OAI
/-! The seven original operand fields on an attained reset actor memory. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSixParty.Chronology.DatePorts DescentOperandCandidateLookup DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {a : PhysicalReset} {w floor : ℕ} (u : a.DateInputs floor w)
set_option quotPrecheck false
local notation "v" => a.successor
local notation "actorBase" => (v).middle.stop (a.rebased floor)
local notation "roots" => a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "rootTicks" => a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits

def ThroughActors (m after : Memory w) : Prop :=
  ((roots).seq ((v).actor.actorBody u.actor actorBase w)).Exec m after
    (rootTicks+(v).actor.actorTicks u.actor actorBase w)

/-- The seven field reads and the kind bound come from one attained register array. -/
def TaggedOrdinals (ok : u.Ready) (small : 2*(v).receiver.candidates<2^(v).receiver.queryBits)
    (after : Memory w) : Prop :=
  ∀j x n,(∀f,Nonempty (OrdinalRead u ok small after ((v).operandOrdinal u.operand f j x n))) ∧
    ∃r : OrdinalRead u ok small after ((v).operandOrdinal u.operand 0 j x n),∀h g,
      (r.kept h g).val+(selected r.query (fun t h g=>((r.raw t h g).val:Cell u.operand.coeff)) h g).val ≤ 2

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
