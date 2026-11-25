import OAI.Hierarchy.DescentStaticWordColumn
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Cheap instructions for the literal word-table installer -/
namespace Hierarchy
open ProtocolRAM

theorem DescentStaticWordColumn.cheap (w base : ℕ) (data : ℕ→ℕ) (n : ℕ) :
    CheapCode (DescentStaticWordColumn.program w base data n) := by
  induction n with
  | zero=>
    intro P R K pc reg pub exit i
    exact scan_cheap w base 0 (.lit 0) pc reg pub exit i
  | succ n ih=>
    intro P R K pc reg pub exit i
    exact cheap_seq ih (scan_cheap w (base+n) 1 (.lit (data n))) pc reg pub exit i

end Hierarchy

end OAI
