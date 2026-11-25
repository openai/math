import OAI.Hierarchy.TaggedWireOriginalSocketExpr
import OAI.Hierarchy.ProtocolRAMRowChoice

namespace OAI
/-! # Expressions selecting the dated physical width, ordinal, and opposite socket -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open ProtocolRAM RoleProgram

inductive RoleField where | width | ordinal | opposite

def RoleField.expr (field : RoleField) (width ordinal opposite : Expr) : Expr :=
  match field with
  | .width=>width
  | .ordinal=>.branch .eq width (.lit 0) (.lit 0) ordinal
  | .opposite=>.branch .eq width (.lit 0) (.lit 0) opposite

namespace DatedRows

def index (n : ℕ) : Expr := .branch .lt .row (.lit n) .row (.op .sub .row (.lit n))

def each (n : ℕ) (left right : Expr) : Expr :=
  .branch .lt .row (.lit n) (left.atRow (index n)) (right.atRow (index n))

def split (n : ℕ) (sock : Bool → Socket) (b : Bool) : Socket :=
  zipSocket (each n) (sock b) (sock (!b))

end DatedRows
end Hierarchy.ProbeStage.CoreBoard.HistoryRoles

end
end OAI
