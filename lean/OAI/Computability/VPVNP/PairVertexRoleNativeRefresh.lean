import OAI.Computability.VPVNP.PairRefreshSelectedDomain
import OAI.Computability.VPVNP.PairRefreshSelectedPublished
import OAI.Computability.VPVNP.PairVertexRoleNativeLeaf

/-! # Exact native refresh execution on the selected vertex domain -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage.RoleDomains

open BurstRAM PrivateRAM Compression CompressorRecords DescriptorSpace LocalHistory TraversalRows TraversalRoles
open DFS TerminalProgram RefreshHook.SelectedRows
open LiveProgram LiveProgram.PairStages LiveProgram.PairStages.Group.Auxiliary
open scoped Fin.CommRing

variable {k : Type} {K : Type*} [_root_.Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → K) (hf : B.IsSolution f) {lanes : ℕ}

section Installed

variable (blocks : ℕ) (budget : blocks * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (branch : (B.execute f hf blocks budget X).Choices) (n hist w start positions : ℕ)
local notation "passes" => executeLevels B f hf blocks budget X branch
local notation "leaf₀" => TaggedLayer.mk (leafLayer (siteOrder X)) Role.cursor
local notation "tags" => TraversalRoles.selected B f hf blocks budget X branch
local notation "first" => endAddress (BlockProgram.layout B start positions blocks)
local notation "rows" => tagWords B.recordLimit tags
local notation "width" => State.totalWidth (StateExecution.finalState (B.execute f hf blocks budget X) branch)
local notation "region" => TerminalLayout.privateRegions (slotDegree S) n (first + rows) hist

/-- Every selected refresh packet is accepted or rejected by the installed
reader exactly as its selected chronological row specifies. -/
theorem nativeRefresh_installed (room : Rooms n hist w start positions blocks (leaf₀) passes)
    (order : B.Entry ≃ Fin hist) (m : Memory w)
    (fit : layerBase B.recordLimit first tags ((passes).length + 1) ≤ 2 ^ w)
    (constants : Constants) (p q : ℕ) {pcs regs : ℕ}
    (V : Placement (TerminalProgram.nativeSegments B constants p q order) pcs regs)
    (M : Machine w pcs regs 11) (contains : Contains V M)
    (published : ∀ x : RefreshHook.SelectedRows.Row passes, (rowSite n hist w start positions blocks width (leaf₀) passes room x).Published
      (RefreshBlockPlan.order B) (PortRefresh.LevelRecipe.Shape.stride (RefreshBlockPlan.shape B)) M.publicData m)
    {data : Fin 10 → Word w} {vals : LeafSourceLoad.Static 34 → Word w}
    {counts : Scratch w n → B.Entry → ℕ} {nodeCap limit : ℕ} :
    (RefreshHook.SelectedRows.parser n hist w start positions blocks width (leaf₀) passes room order M.publicData m).ExactOn
      (Domain X B.recordLimit first passes region data ((rows + width : ℕ) : Word w) vals counts nodeCap limit .refresh)
      M (V.entry .refresh) (V.dfsPC 3) V.dfs m :=
  restrict (RefreshHook.SelectedRows.exactOn n hist w start positions blocks width (leaf₀) passes room
    order m fit constants p q V M contains published)
    fun _ _ h => prepared_of_domain B f hf blocks budget X branch n hist w start positions room h

end Installed

section Physical

variable {n hist : ℕ} (G : LiveProgram.PairStages.Group) (workspace : Word G.w) (positions blocks : ℕ)
    (budget : blocks * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (branch : (B.execute f hf blocks budget X).Choices)
local notation "layout" => BlockProgram.layout B workspace.val positions blocks
local notation "passes" => executeLevels B f hf blocks budget X branch
local notation "leaf₀" => TaggedLayer.mk (leafLayer (siteOrder X)) Role.cursor
local notation "tags" => TraversalRoles.selected B f hf blocks budget X branch
local notation "rows" => tagWords B.recordLimit tags
local notation "width" => State.totalWidth (StateExecution.finalState (B.execute f hf blocks budget X) branch)
local notation "region" => TerminalLayout.privateRegions (slotDegree S) n (endAddress layout + rows) hist

/-- The current linked vertex memory supplies all row publications from
the physical entry and the selected calendar history. -/
theorem nativeRefresh {tab : Fin (layout).shape.tables} {baseBits laneBits ordinal : ℕ}
    {calendar vertex current : Memory G.w} {wireBits : Fin width → Bool}
    (entry : VertexEntry B f hf blocks budget X branch layout tab baseBits laneBits (terminalOperands G)
      calendar vertex wireBits)
    (history : SelectedPayloadHistory.Past B f hf layout (CompiledResident.payload B f hf workspace positions blocks n)
      passes calendar)
    (packed : VertexPacked G layout B.recordLimit tags width) (frame : LinkedVertexMemory G vertex ordinal current)
    (room : Rooms n hist G.w workspace.val positions blocks (leaf₀) passes)
    (p q : ℕ) (order : B.Entry ≃ Fin hist) {data : Fin 10 → Word G.w}
    {vals : LeafSourceLoad.Static 34 → Word G.w} {counts : Scratch G.w n → B.Entry → ℕ} {nodeCap limit : ℕ} :
    let segments := TerminalProgram.nativeSegments B G.constants p q order
    let V := placement segments
    let M := (template segments).instantiate G.w (terminalOperands G)
    (RefreshHook.SelectedRows.parser n hist G.w workspace.val positions blocks width (leaf₀) passes room order
      (terminalOperands G) current).ExactOn
      (Domain X B.recordLimit (endAddress layout) passes region data ((rows + width : ℕ) : Word G.w)
        vals counts nodeCap limit .refresh) M (V.entry .refresh) (V.dfsPC 3) V.dfs current :=
  restrict (exact_at_site B f hf G workspace positions blocks budget X branch entry history packed frame room p q order)
    fun _ _ h => prepared_of_domain B f hf blocks budget X branch n hist G.w workspace.val positions room h

end Physical

end PairSimulation.VertexImage.RoleDomains

end VPVNP
end Computability
end OAI
