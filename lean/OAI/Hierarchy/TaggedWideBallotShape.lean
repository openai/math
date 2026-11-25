import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Rows, parties and word columns of a physical ballot archive -/

namespace Hierarchy.ProtocolRAM.Calendar.WideCPU

/-- One chronological ballot archive. The shape is fixed by the row type of the
calendar event. After all ballot archives, the same emitter with one candidate
per site produces the common passive/gather controls for that site. -/
structure Shape where
  candidates : ℕ
  parties : ℕ
  columns : ℕ

def Shape.count (p : Shape) := p.candidates*(p.parties*p.columns)
def Shape.advice (p : Shape) (sites : ℕ) := 3*p.count+sites
def Shape.span (p : Shape) (sites : ℕ) := 1+sites*p.columns+2*p.count

structure Fields (p : Shape) where
  selected : Fin p.parties → Expr
  site : Fin p.parties → Expr
  value : Fin p.parties → Fin p.columns → Expr

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end OAI
