import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! The native address expression for a fixed list of source digits. -/
namespace Hierarchy.DescentTerminalVertexFields
open ProtocolRAM
def sumExpr {ι : Type} (r : ι→Expr) : List ι→Expr
  | []=>.lit 0
  | i::tail=>.op .add (r i) (sumExpr r tail)

end Hierarchy.DescentTerminalVertexFields

end OAI
