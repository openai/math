import OAI.Hierarchy.DescentTerminalHomeFormat
import OAI.Hierarchy.DescentTerminalCohortSize

namespace OAI
/-! # Fixed dimensions of the nine measured terminal channel widths -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open DescentTerminalVertexFields
noncomputable section
def fieldSum (v : Home.Format) (blocks : ℕ) :=
  ∑j:Fin (channels blocks),channelSize (q:=v.publicArity) (t:=v.roles) (H:=v.privateWords)
    (N:=v.nodes) (A:=v.addresses) (w:=v.piece) (groups:=v.groups) j

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
