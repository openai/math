import OAI.Hierarchy.DescentTerminalHeaderPrefixRAM
import OAI.Hierarchy.DescentTerminalExecUnique

namespace OAI
/-! # Defined memory and exact costs for the prefix scan on an arbitrary proposed header -/
namespace Hierarchy.DescentTerminalHeaderPrefixRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Fin.CommRing
noncomputable section
variable {w : ℕ}
def stateOn (op : Op) (rowExpr : Expr) (m : Memory w) : ℕ→Word w
  | 0=>0
  | i+1=>value op m (stateOn op rowExpr m i) (rowExpr.eval m (i:Word w))

def result (out n : ℕ) (op : Op) (rowExpr : Expr) (m : Memory w) :=
  fillSegment out n (file out (stateOn op rowExpr m)) m

theorem exec_any (out n : ℕ) (op : Op) (rowExpr : Expr) (m : Memory w) (ofit : Fits op w out)
    (rfit : rowExpr.Fits w out) (endAt : out+n<2^w) :
    (program w out n op rowExpr).Exec m (result out n op rowExpr m) (4+n*(2*work op rowExpr+4)) :=
  spec out op rowExpr m (stateOn op rowExpr m) ofit rfit endAt rfl (fun _=>rfl)

end
end Hierarchy.DescentTerminalHeaderPrefixRAM

end OAI
