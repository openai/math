import OAI.Computability.VPVNP.PairRefreshSelectedParser
import OAI.Computability.VPVNP.PairRefreshHookGuard

/-! # Resident data for a selected refresh level -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.SelectedRows

open BurstRAM PrivateRAM Compression CompressorRecords DescriptorSpace PortRefresh
open PortRefresh.NewSlots TraversalRows TraversalRoles LocalHistory NetworkKernel NodeArguments
open TreeDecode VertexImage DFS
open LiveProgram Filter
open scoped Fin.CommRing
set_option quotPrecheck false

variable {k K : Type} [_root_.Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → K) (hf : B.IsSolution f) {hist : ℕ}
    {lanes : ℕ} (blocks : ℕ) (budget : blocks * S.laneBits ≤ lanes)
    (X : State (S.degreeExponent 0) lanes) (branch : (B.execute f hf blocks budget X).Choices)
    (n w start positions width : ℕ)
local notation "passes" => executeLevels B f hf blocks budget X branch
local notation "leaf₀" => TaggedLayer.mk (leafLayer (siteOrder X)) Role.cursor
local notation "first" => endAddress (BlockProgram.layout B start positions blocks)
local notation "tags₀" => selected B f hf blocks budget X branch
local notation "rows" => tagWords B.recordLimit (tags₀)
local notation "region" => TerminalLayout.privateRegions (slotDegree S) n (first + rows) hist
variable (room : Rooms n hist w start positions blocks ⟨leafLayer (siteOrder X), .cursor⟩
    (executeLevels B f hf blocks budget X branch))
local notation "site" => rowSite n hist w start positions blocks width (leaf₀) passes room
local notation "ties₀" => RefreshBlockPlan.order B
local notation "stride₀" => LevelRecipe.Shape.stride (RefreshBlockPlan.shape B)

/-- Memory and capacity facts at the start of the selected vertex.
The physical head bounds include the saved traversal directory and role tags. -/
structure LevelMemory (pub : Fin 11 → Word w) (m : Memory w) : Prop where
  tags : TraversalRoles.Reads w m (rows + width) B.recordLimit first (tags₀)
  tagEnd : (rows + width) + first + rows ≤ (TerminalLink.header pub).val
  headerFit : (TerminalLink.header pub).val + 31 < 2 ^ w
  codes : 2 < 2 ^ w
  cacheFit : (region).cacheBase + 38 ≤ 2 ^ w
  published : ∀ x, (site x).Published (ties₀) (stride₀) pub m
  layout : ∀ x, ∃ prev next, Site.GuardLayout B (site x) pub m start positions blocks prev next
  later : ∀ x, (site x).later ≤ (S.steps + 1) * (n.log2 + 1)

end PairSimulation.RefreshHook.SelectedRows

end VPVNP
end Computability
end OAI
