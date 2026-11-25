import OAI.Hierarchy.DescentTerminalBookROM
import OAI.Hierarchy.DescentTerminalBinPack

namespace OAI
/-! # The occupied row count of a bounded terminal incidence book -/
namespace Hierarchy.DescentTerminalLocalPortBook
open Computability.VPVNP.BurstRAM DescentTerminalBinPack ThreeFlat.Routing
open scoped BigOperators Fin.CommRing
noncomputable section
variable {G V M A a w : ℕ}
def Book.rows (bk : Book G V M A a) (q : ℕ) := (∑g,poolBatchCount (bk.size g) q)+bins q bk.arity+1

def countTable (q : ℕ) (i : Fin (Book.Bytes G V M A a)) :=
  ((Book.fromBytes i : Book G V M A a).rows q : Word w)

end
end Hierarchy.DescentTerminalLocalPortBook

end OAI
