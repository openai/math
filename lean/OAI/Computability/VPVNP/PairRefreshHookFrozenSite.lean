import OAI.Computability.VPVNP.PairRefreshHookVertexPublished
import OAI.Computability.VPVNP.PairTerminalSiteDirectories

/-!
# The refresh hook after preceding physical site calls

The linked site's external memory preserves the selected history, placement
pointers and DFS rows from the completed vertex entry. These facts recover
the published refresh hook after earlier sites have flushed their motif counts.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.RefreshHook.SelectedPublished

open BurstRAM Compression Compression.Refresh CompressorRecords PortRefresh NewSlots
open LocalHistory TraversalRoles TraversalRows DescriptorSpace TerminalProgram
open LiveProgram.PairStages LiveProgram.PairStages.Group.Auxiliary
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
  {A : Type*} [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f)
  {n l g hist : ℕ} (G : LiveProgram.PairStages.Group) (workspace : BurstRAM.Word G.w)
  (positions blocks : ℕ)
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
theorem at_site {tab : Fin (layout).shape.tables} {baseBits laneBits ordinal : ℕ}
    {calendar vertex current : Memory G.w} {wireBits : Fin width → Bool}
    (entry : VertexEntry B f hf blocks budget initial branch layout tab baseBits laneBits
      (terminalOperands G) calendar vertex wireBits)
    (history : SelectedPayloadHistory.Past B f hf layout
      (CompiledResident.payload B f hf workspace positions blocks n) levels calendar)
    (packed : VertexPacked G layout cap tags width)
    (frame : LinkedVertexMemory G vertex ordinal current)
    (fits : TraversalPlan.Room B X choice port (slotDegree S) n rowEnd child parent hist G.w) :
    let R := ofSelected B n hist G.w workspace.val positions blocks X choice port stage.val
      tags width fits
    R.Published (RefreshBlockPlan.order B) (RefreshBlockPlan.shape B).stride
      (terminalOperands G) current := by
  have lastLive : (selectedLayers B f hf blocks budget initial branch).dropLast.length <
      (layout).levels := by
    rw [TerminalBootstrap.selected_prior_length, BlockProgram.actual_level_count,
      Nat.mul_comm blocks]
    omega
  have allLive : (levels).length < (layout).levels :=
    (executeLevels_length B f hf blocks budget initial branch).trans_lt (by
      rw [BlockProgram.actual_level_count]
      omega)
  have prior := entry.payload B f hf blocks budget initial branch lastLive history
  obtain ⟨⟨ds, resident⟩, past⟩ := packed.site_operands frame entry allLive
    (by change 28 ≤ 54; decide) prior
  have data := RefreshHookRetained.ofPast B f hf workspace positions blocks n X choice past
    stage record occurrence
  have layerEq := selected_layers B f hf blocks budget initial branch
  have rowMem := packed.rows frame (layerEq ▸ selected_capacity B f hf blocks budget initial branch)
    (layerEq ▸ entry.rows)
  rw [layerEq] at rowMem
  exact from_resident B f hf blocks budget initial branch X choice record port stage occurrence
    workspace.val positions blocks fits data.size data.live ds resident rowMem data.sources
    data.child

end PairSimulation.RefreshHook.SelectedPublished

end

end VPVNP
end Computability
end OAI
