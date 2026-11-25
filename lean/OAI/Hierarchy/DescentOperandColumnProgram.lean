import OAI.Hierarchy.DescentPackedColumnBatch
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Code size of fixed counted packed-column passes -/
namespace Hierarchy.DescentPackedFlowBatch
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
variable {w base : ℕ}
theorem program_bound (rows pitch start n : ℕ) (e : ℕ→Expr) (K : ℕ)
    (limit : ∀j,start≤j→j<start+n→(e j).work≤K) :
    DescentStaticWordColumn.names (ProtocolRAM.program w (passes base rows pitch e start n))
      ≤15+n*(11+4*K) :=by
  induction n generalizing start with
  | zero=>
    change DescentStaticWordColumn.names (scan w 0 0 (.lit 0))≤_
    rw [DescentStaticWordColumn.names_scan]
    simp [Expr.work]
  | succ n ih=>
    have tail:=ih (start+1) (fun j lo hi=>limit j (by omega) (by omega))
    have head:=limit start (by omega) (by omega)
    change DescentStaticWordColumn.names ((scan w (base+start*pitch) rows (e start)).seq
      (ProtocolRAM.program w (passes base rows pitch e (start+1) n)))≤_
    rw [DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_scan, Nat.succ_mul n (11+4*K)]
    omega
end Hierarchy.DescentPackedFlowBatch

end OAI
