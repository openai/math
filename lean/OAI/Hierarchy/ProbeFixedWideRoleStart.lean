import OAI.Hierarchy.ProbeFixedWideSettlementPage
import OAI.Hierarchy.ProtocolRAMCatalystTerminalUpper

namespace OAI
/-! # Beginning of the role bank in the fixed physical calendar -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM CatalystArchive
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "A" => v.privateArena (v.widePlacement h width) h width
local notation "sheet" => v.wideSignedPage h width

/-- The signed bank begins after all paid output stages and the full original finite
calendar tape. Its size includes each of the physical positive and stock entries. -/
def wideRoleStart (stock : Bank) (slices : List PaidWidths.Slice) :=
  max ((A).endAddress v.mesh) (TerminalLayout.extent (sheet stock) slices)


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
