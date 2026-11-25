import OAI.Hierarchy.ProtocolRAMRowChoice
import OAI.Hierarchy.ProtocolRAMOccurrenceHeader

namespace OAI
/-! # Stock-bank destination of a physical strip occurrence -/

namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
variable {w : ℕ}

/-- Relative destination in the global stock bank for an actual occurrence.
Noncommodity wires and their charges are assigned the separate sentinel. -/
def destination (h : Calendar.StockCommit.PortHeader) (global : ℕ)
    (slot : Fin h.ports → Option Expr) : Expr :=
  chooseField h.ports 0 (fun e => ((slot e).getD (.lit global)).atRow h.ballTerm) h.fieldTerm

theorem destination_read (h : Calendar.StockCommit.PortHeader) (global : ℕ)
    (slot : Fin h.ports → Option Expr) (mem : Memory w) (r : Word w)
    (e : Fin h.ports) (room : h.ports≤2^w) (hit : (h.fieldTerm.eval mem r).val=e.val) :
    (destination h global slot).eval mem r =
      ((slot e).getD (.lit global)).eval mem (h.ballTerm.eval mem r) := by
  rw [destination,eval_chooseField _ _ _ _ _ _ e (by simpa using room) (by simpa using hit),eval_atRow]

end
end Hierarchy.ProtocolRAM.StripDirectory

end OAI
