import Mathlib.Data.List.OfFn

namespace OAI
/-! # Literal weight words of the six mixed-radix parts -/
namespace Hierarchy.DescentTerminalPrintedFieldsRAM
def weights (cap stride : ℕ) := List.ofFn (fun i : Fin cap=>i.val*stride)
end Hierarchy.DescentTerminalPrintedFieldsRAM

end OAI
