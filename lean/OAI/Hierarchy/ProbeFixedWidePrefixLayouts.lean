import OAI.Hierarchy.ProbeFixedWideRoleStart
import OAI.Hierarchy.ProbeFixedTerminalStock
import OAI.Hierarchy.TaggedWideAddressShape
import OAI.Hierarchy.TaggedWireRoleRoomShape
import OAI.Hierarchy.ProtocolRAMCalendarPrefixLayout

namespace OAI
/-! # Addresses of the dated width and reserve banks for the fixed calendar -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CatalystArchive
open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "D" => 2^v.W
local notation "num" => Fintype.card (Columns h D)*k
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "rows" => (P).catalogue.rows
local notation "sizes" => RoleRoom.shape (R:=WideMemory.R v.sampler h v.W k) v.sampler directory rows
local notation "last" => (events v.mesh).length

def wideRoleSize (stock : Bank) (slices : List PaidWidths.Slice) :=
  (sizes).ceiling (v.wideRoleStart h width stock slices)

local notation "stock" => v.fixedTerminalStock P h width

def wideWidthLayout (ss : List PaidWidths.Slice) : PrefixWidths.Layout rows :=
  PrefixWidths.Layout.packed rows (v.wideRoleSize h width stock ss) ((rows).log2+1) last (Nat.lt_log2_self.le)

def wideReserveLayout (ss : List PaidWidths.Slice) : PrefixWidths.Layout num :=
  (v.wideWidthLayout h width ss).reserveLayout ((num).log2+1) last (Nat.lt_log2_self.le)


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
