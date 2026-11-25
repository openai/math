import OAI.Hierarchy.TaggedWidePlacement
import OAI.Hierarchy.TaggedWirePaidRoleRead
import OAI.Hierarchy.TaggedWireRoleRoomShape

namespace OAI
/-! # Original socket operands and bought-row numbering of the fixed wide placement -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets
open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
open BoughtSockets PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
variable (h width : ℕ)
set_option quotPrecheck false
local notation "D" => 2^v.W
local notation "P" => v.widePlacement h width
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "G" => (directory).groups
local notation "rows" => (P).catalogue.rows
local notation "z" => RoleRoom.shape («R»:=R) v.sampler directory rows
local notation "base" => CoreCatalogue.headBase h v.W K G H
local notation "super" => CoreCatalogue.superStart h v.W
local notation "bits" => CoreCatalogue.pointBits h v.W
local notation "published" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K G H R


/-- The native core/bought interval selector applied to its original two socket descriptors. -/
def widePaidPorts (start : ℕ) :=
  paidInputs (P).catalogue (coreInputs base ((z).free start) R bits super K k v.wideJobs)
    (boughtInputs published v.sampler h v.W k v.depth K)

/-- The acquired catalogue points at the dated shelf and its local DFS ordinal. -/
def wideBoughtOrdinal (π : Equiv.Perm (Fin (2^h))) (marks : Marks h v.W k v.wideJobs)
    (e : Bought v.sampler π v.depth marks) : Fin (P).catalogue.boughtRows :=
  ((published).header h D k v.sampler.degree v.depth).enum ⟨e.1,BoughtLocation.relative e.2⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
