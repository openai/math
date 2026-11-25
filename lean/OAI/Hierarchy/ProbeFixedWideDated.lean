import OAI.Hierarchy.ProbeFixedBroadcastCap
import OAI.Hierarchy.ProbeFixedWideRoleExpressions
import OAI.Hierarchy.ProbeFixedWideTerminalBoard
import OAI.Hierarchy.TaggedWideDatedLayout
import OAI.Hierarchy.ProbeFixedWidePacketFields
import OAI.Hierarchy.TaggedWideMountedControlFields
import OAI.Hierarchy.ProbeFixedWideNeighborCapacity

namespace OAI
/-! # Fixed native site and history table layout of the calibrated controller -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard StripChart
open HistoryRoles RoleProgram WideCPU Tagged CatalystArchive
open scoped Classical Fin.CommRing BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "D" => 2^v.W
set_option quotPrecheck false in
local notation "edges" => (P).catalogue.rows
local notation "dates" => events v.mesh
local notation "sites" => siteLast h D k+1
local notation "degree" => HistoryRoles.stride k v.sampler.degree v.wideJobs
local notation "original" => Fintype.card (Old h v.W k edges)
local notation "B" => v.wideTerminalBoard h width v.maxBits 0
local notation "dst" => TerminalLayout.destination (v.wideSignedPage h width (v.fixedTerminalStock P h width))

/-- All chronological party, role and field ordinals are public. The elected
ballot, actual rooted strip sites, online histogram and measured role quantities
are loaded by the fixed program. -/
def wideDated (ell unitCost : ℕ) : WideCPU.Dated (dates).length where
  «sites» := sites
  physical := original
  roleCount := degree
  chart := (B).chart
  sockets := (B).before
  siteDirectorySize := SiteDirectory.size h D k
  amount j := v.wideRoleWidth h width v.maxBits j.val
  ordinal := v.wideRoleID h width v.maxBits
  ballot j := v.widePacketShape h width ((dates).get j)
  controlColumns _ := SiteControls.fieldCount degree
  fields j siteBase table old new := v.widePacketFields h width (ProtocolRAMPurchaseSampler.bits (sites*degree))
    ((dates).get j) siteBase table old new
  controls j table old new ballotBase := SiteControls.fixed sites original degree (v.wideNeighborCap width unitCost)
    table old new ballotBase (v.widePacketShape h width ((dates).get j)).columns (v.widePacketLowStart h width ((dates).get j))
  rawEdges := edges
  measured := RoleROM.bank (dst+3*edges+1) (3*edges)
  lanes := 2^ell
  orderedSlot side := (normalized (B).chart (B).finish side).slot

theorem wide_dated_sites (ell unitCost : ℕ) :
    (v.wideDated h width ell unitCost).siteDirectorySize=SiteDirectory.size h D k := rfl

theorem wide_dated_edges (ell unitCost : ℕ) :
    (v.wideDated h width ell unitCost).rawEdges=edges := rfl

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
