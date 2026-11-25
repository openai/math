import OAI.Hierarchy.DescentPhysicalResetDateOutput
import OAI.Hierarchy.DescentResetFundedTaps

namespace OAI
/-! The stable pre-projection window in the real operand-date output. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentFallbackPeriod DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "root" => a.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w
local notation "stencil" => a.throughStencil u.shape floor u.count u.hub u.g u.Y u.src u.sourceRows u.oldDegree w
local notation "time₀" => a.throughStencilTicks u.shape floor u.count u.hub u.g u.Y u.sourceRows u.oldDegree w

/-- The complete scheduled operand run and the actual preceding chosen-stencil run
determine every earlier signed input word, through the entire original root book. -/
theorem projection_after (ready : u.Ready) {before measured out : Memory w}
    (scanned : (stencil).Exec before measured time₀) (operands : u.throughOperandDate.Runs before out) :
    ∀i,i<(root).projectionEnd→ out i=(root).prefixImage u.bookFits.toPrefixFits measured i:=by
  have limits:=u.book.limits (root).projectionEnd a.successor.middle.signedHosts
    (2^a.successor.middle.stencil.c) a.successor.middle.signedLanes
  have shelf:(root).projectionEnd≤(root).preparedEnd u.book:=
    (limits.1.trans (limits.2.1.trans limits.2.2)).trans (Nat.le_add_right ..)
  have run:=(root).prepared_any u.book u.bookFits measured
  intro i hi
  have historical:=u.prefix_unchanged ready (afterRoots:=(root).preparedImage u.book u.bookFits measured)
    (by intro P R K mach;exact Procedure.Exec.then scanned run.1 mach) operands i (hi.trans_le shelf)
  exact historical.trans ((root).prepared_window u.book u.bookFits measured i hi)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
