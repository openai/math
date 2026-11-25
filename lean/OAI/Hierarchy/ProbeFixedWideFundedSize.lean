import OAI.Hierarchy.ProbeFixedWidePrefixLayouts
import OAI.Hierarchy.ProbeFixedWideEventCode

namespace OAI
/-! # Size of the wide input carrying the signed roles and paid event slices -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "stock" => v.fixedTerminalStock P h width
local notation "ss" => v.widePaidSlices h width

def wideFundedSize (bits : ℕ) := v.wideRoleSize h width stock (ss bits)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
