import OAI.Hierarchy.DescentTerminalPrintedFields

namespace OAI
/-! # The numerical empty-or-occupied terminal shelf code -/
namespace Hierarchy
noncomputable section
open DescentTerminalRowBooks DescentTerminalPrintedFields
variable {q t H N A w V : ℕ}

def DescentTerminalChronologicalIssue.present (c : Control q t H N A w V) : Option (Control q t H N A w V) :=
  if c.1.val=0 then none else some c

def DescentTerminalLeafFold.code (z : Option (Control q t H N A w V)) :=
  (z.map fun c=>(serial (capacity q t H N A w V) (digits (emit c))).val).getD 0

end
end Hierarchy

end OAI
