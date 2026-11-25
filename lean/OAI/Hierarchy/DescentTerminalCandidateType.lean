import OAI.Hierarchy.DescentTerminalBinReaddress

namespace OAI
/-! # Coordinates of the original chip, paid bits, and complete terminal candidate -/
namespace Hierarchy.DescentTerminalChipPins
open DescentTerminalBinReaddress

abbrev Bit (K W q p : ℕ) := Fin K × Slot W q × Fin (W*p)
abbrev Inputs (K W q p : ℕ) := Bool × Bit K W q p

end Hierarchy.DescentTerminalChipPins

namespace Hierarchy.DescentTerminalPorts

abbrev RowBit (rows word : ℕ) := Fin rows × Fin word

end Hierarchy.DescentTerminalPorts

namespace Hierarchy.DescentTerminalFullPins
open DescentTerminalChipPins DescentTerminalPorts

abbrev Candidate (old : Type) (K W q piece rows : ℕ) :=
  (old ⊕ Inputs K W q piece) ⊕ RowBit rows (q*(W*piece))

end Hierarchy.DescentTerminalFullPins

end OAI
