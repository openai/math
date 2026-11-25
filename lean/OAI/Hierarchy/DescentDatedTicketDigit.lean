import OAI.Hierarchy.DescentPackedSourceAccess
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Read the scalar ticket value at its actual packed lane -/
namespace Hierarchy.DescentDatedOperandCoordinates.Ticket
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
def socketDigit {H G w : ℕ} (field M : ℕ) (expr : Expr) (m : Memory w) (h : Fin H) (g : Fin G) :=
  digit field (g.val%M) (expr.eval m ((g.val/M+chunks G M*h.val:ℕ):Word w)).val

theorem socket_digit {field M H G w : ℕ} (expr : Expr) (m : Memory w) (v : Fin H→Fin G→Cell field)
    (reads : Source expr v M m) (pitch : 0 < M) (bits : field*M ≤ w) (h : Fin H) (g : Fin G) :
    socketDigit field M expr m h g=(v h g).val :=by
  have stored:=DescentSixParty.Chronology.PackedSource.read v (fun n=>expr.eval m (n:Word w)) 0 pitch bits
    (fun p=>by simpa only [Nat.zero_add] using reads p) h g
  simpa only [socketDigit,Nat.zero_add] using stored
end
end Hierarchy.DescentDatedOperandCoordinates.Ticket

end OAI
