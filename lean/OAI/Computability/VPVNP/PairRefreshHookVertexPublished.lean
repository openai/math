import OAI.Computability.VPVNP.PairRefreshHookSelectedPublished
import OAI.Computability.VPVNP.CompressorRefreshHookRetained

/-!
# The selected refresh hook at entry into the physical vertex traversal

Each selected occurrence recovers its actual compressor payload from the
calendar history. The linked traversal and shared-bit stages have already
constructed the directory words and DFS rows in the vertex-entry memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.RefreshHook.SelectedPublished

open BurstRAM Compression Compression.Refresh CompressorRecords PortRefresh NewSlots
open LocalHistory TraversalRoles TraversalRows DescriptorSpace TerminalProgram
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
  {A : Type*} [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f)
  {n l w g hist : ℕ} (workspace : BurstRAM.Word w) (positions blocks : ℕ)
  (budget : blocks * S.laneBits ≤ l) (initial : State (S.degreeExponent 0) l)
  (branch : (B.execute f hf blocks budget initial).Choices)
  (X : State S.portExponent (S.portExponent + g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (record : List Bool) (port : (X.Base × BitWord g) × Fin (2 ^ S.portExponent))
  (stage : Fin (executeLevels B f hf blocks budget initial branch).length)
  (occurrence : (executeLevels B f hf blocks budget initial branch)[stage] =
    RefreshPlacement.traversalLevel f hf X choice record)

local notation "layout" => BlockProgram.layout B workspace.val positions blocks
local notation "levels" => executeLevels B f hf blocks budget initial branch
local notation "tags" => TraversalRoles.selected B f hf blocks budget initial branch
local notation "cap" => BlockSchedule.Templates.recordLimit B
local notation "first" => endAddress layout
local notation "rowEnd" => first + tagWords cap tags
local notation "ord" => Fin.val (sites X.baseIndex (bitWordFinEquiv g) port)
local notation "child" => address cap (layerBase cap first tags stage.val) ord
local notation "parent" => address cap (layerBase cap first tags (stage.val + 1)) ord
local notation "width" =>
  State.totalWidth (StateExecution.finalState (B.execute f hf blocks budget initial) branch)

include occurrence in
/-- The four linked terminal stages and the actual selected calendar suffice for the
whole publication invariant, with no individually assumed graph or directory cells. -/
theorem of_vertex_entry {tab : Fin (layout).shape.tables} {baseBits laneBits : ℕ}
    {pub : Fin 11 → BurstRAM.Word w} {calendar vertex : Memory w}
    {wireBits : Fin width → Bool}
    (entry : VertexEntry B f hf blocks budget initial branch layout tab baseBits laneBits
      pub calendar vertex wireBits)
    (history : SelectedPayloadHistory.Past B f hf layout
      (CompiledResident.payload B f hf workspace positions blocks n) levels calendar)
    (fits : TraversalPlan.Room B X choice port (slotDegree S) n rowEnd child parent hist w) :
    let R := ofSelected B n hist w workspace.val positions blocks X choice port stage.val
      tags width fits
    R.Published (RefreshBlockPlan.order B) (RefreshBlockPlan.shape B).stride pub vertex := by
  have data := RefreshHookRetained.atVertex B f hf workspace positions blocks n X choice budget
    initial branch entry history stage record occurrence
  obtain ⟨ds, resident⟩ := entry.directories
  exact from_resident B f hf blocks budget initial branch X choice record port stage occurrence
    workspace.val positions blocks fits data.size data.live ds resident entry.rows data.sources
    data.child

end PairSimulation.RefreshHook.SelectedPublished

end

end VPVNP
end Computability
end OAI
