import OAI.Computability.VPVNP.PairRefreshSelectedRows
import OAI.Computability.VPVNP.PairRefreshHookFrozenSite

/-! # Native refresh execution at every physical terminal vertex

The calendar payload and the linked memory of the current vertex provide the
published fields of each row decoded by the chronological parser. This also
covers vertices reached after earlier calls have flushed their motif counts.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.SelectedRows

open BurstRAM BurstRAM.PrivateRAM Compression CompressorRecords DescriptorSpace
open TraversalRows TraversalRoles ShrinkRoleDirectory LocalHistory TerminalProgram VertexImage DFS
open LiveProgram LiveProgram.PairStages LiveProgram.PairStages.Group.Auxiliary
open scoped Fin.CommRing
set_option maxHeartbeats 1500000

variable {k : Type} {K : Type*} [_root_.Field k] [CommRing K] {S : BlockSchedule k} (B : S.Templates)
  (f : B.Entry → K) (hf : B.IsSolution f) {n l hist : ℕ} (G : LiveProgram.PairStages.Group)
  (workspace : Word G.w) (positions blocks : ℕ) (budget : blocks * S.laneBits ≤ l)
  (initial : State (S.degreeExponent 0) l) (branch : (B.execute f hf blocks budget initial).Choices)
local notation "L₀" => BlockProgram.layout B workspace.val positions blocks
local notation "passes₀" => executeLevels B f hf blocks budget initial branch
local notation "leaf₀" => TaggedLayer.mk (leafLayer (siteOrder initial)) Role.cursor
local notation "tags₀" => TraversalRoles.selected B f hf blocks budget initial branch
local notation "width₀" => State.totalWidth (StateExecution.finalState (B.execute f hf blocks budget initial) branch)
local notation "pub₀" => terminalOperands G
variable {tab : Fin (BlockProgram.layout B workspace.val positions blocks).shape.tables}
  {baseBits laneBits ordinal : ℕ} {calendar vertex current : Memory G.w}
  {wireBits : Fin ((StateExecution.finalState (B.execute f hf blocks budget initial) branch).totalWidth) → Bool}
  (entry : VertexEntry B f hf blocks budget initial branch
    (BlockProgram.layout B workspace.val positions blocks) tab baseBits laneBits (terminalOperands G) calendar vertex wireBits)
  (history : SelectedPayloadHistory.Past B f hf (BlockProgram.layout B workspace.val positions blocks)
    (CompiledResident.payload B f hf workspace positions blocks n) (executeLevels B f hf blocks budget initial branch) calendar)
  (packed : VertexPacked G (BlockProgram.layout B workspace.val positions blocks) B.recordLimit
    (TraversalRoles.selected B f hf blocks budget initial branch)
    (State.totalWidth (StateExecution.finalState (B.execute f hf blocks budget initial) branch)))
  (frame : LinkedVertexMemory G vertex ordinal current)
  (room : Rooms n hist G.w workspace.val positions blocks (TaggedLayer.mk (leafLayer (siteOrder initial)) Role.cursor)
    (executeLevels B f hf blocks budget initial branch))
local notation "site₀" => rowSite n hist G.w workspace.val positions blocks (width₀) (leaf₀) (passes₀) room

include entry history packed frame in
/-- Readback for all rows of this selected branch, directly at the site's
external memory. -/
theorem published_at_site (x : Row (passes₀)) : ((site₀) x).Published (RefreshBlockPlan.order B)
    (PortRefresh.LevelRecipe.Shape.stride (RefreshBlockPlan.shape B)) (pub₀) current :=
  SelectedPublished.at_site B f hf G workspace positions blocks budget initial branch
    x.occurrence.state x.occurrence.choice passes₀[x.val.1].selector x.occurrence.port x.val.1
    x.occurrence.selected entry history packed frame (room x)

variable (p q : ℕ) (order : B.Entry ≃ Fin hist)
local notation "segments₀" => TerminalProgram.nativeSegments B G.constants p q order
local notation "reader₀" => SelectedRows.parser n hist G.w workspace.val positions blocks (width₀) (leaf₀) (passes₀) room order (pub₀) current
local notation "domain₀" => Prepared n hist G.w workspace.val positions blocks (width₀) (leaf₀) (passes₀) room

include entry history packed frame in
/-- At an arbitrary site of the completed calendar, the full fixed numerical
table realizes the refresh reader for every prepared chronological row. -/
theorem exact_at_site :
    let V := placement (segments₀)
    let M := (template (segments₀)).instantiate G.w (pub₀)
    (reader₀).ExactOn (domain₀) M (V.entry .refresh) (V.dfsPC 3) V.dfs current := by
  intro V M
  have len : (passes₀).length + 1 = (tags₀).length := by
    simp [TraversalRoles.selected]
  have fit : layerBase B.recordLimit (endAddress (L₀)) (tags₀) ((passes₀).length + 1) ≤ 2^G.w := by
    rw [len, layerBase, List.take_length]
    change endAddress (L₀) + tagWords B.recordLimit (tags₀) ≤ _
    have bound := packed.arena
    have headerRoom := packed.room
    omega
  apply exactOn n hist G.w workspace.val positions blocks (width₀) (leaf₀) (passes₀) room order
    current fit G.constants p q V M (template_contains (segments₀) (pub₀))
  exact published_at_site B f hf G workspace positions blocks budget initial branch entry history packed frame room

end PairSimulation.RefreshHook.SelectedRows

end VPVNP
end Computability
end OAI
