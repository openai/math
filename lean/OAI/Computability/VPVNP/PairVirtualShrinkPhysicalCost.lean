import OAI.Computability.VPVNP.PairVirtualShrinkRowCost
import OAI.Computability.VPVNP.PairShrinkPhysicalSiteBank
import OAI.Computability.VPVNP.PairShrinkHookActionRates

/-!
# The native probe and instruction charges at a shrinking occurrence

The level locator, old wires and child order are those of the history
published for this vertex. The raw row includes room for the dispatch
probe and its nine instructions. The dispatched job satisfies the single
rate used by the complete terminal reader.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkRole

open BurstRAM Compression CompressorRecords DescriptorSpace DFS LocalHistory
open LiveProgram.PairStages LiveProgram.PairStages.Group.Auxiliary TraversalRows TraversalRoles
open VertexImage

variable {K A : Type} [_root_.Field K] [CommRing A] {S : BlockSchedule K}
  (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
  {lanes T : ℕ} (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
  (z : (B.execute f hf T hT X).Choices) {G : Group} {n limit : ℕ}
  (order : B.Entry ≃ Fin (Fintype.card B.Entry)) (budget : RowBudget B order X n G.w T)

set_option quotPrecheck false
local notation "pub" => terminalOperands G
local notation "L" => BlockProgram.layout B (pub 2).val X.positions T
local notation "passes" => executeLevels B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z
local notation "rowEnd" => endAddress L+words B.recordLimit (selectedLayers B f hf T hT X z)
local notation "earlier" j => layerBase B.recordLimit (endAddress L) tags j
local notation "sites" => ShrinkRoleDirectory.ShrinkSite passes

variable {table : Fin (BlockProgram.layout B (terminalOperands G 2).val X.positions T).shape.tables}
  {baseBits laneBits ord : ℕ} {calendar reference m : Memory G.w}
  {bits : Fin (StateExecution.finalState (B.execute f hf T hT X) z).totalWidth → Bool}
  (history : SelectedPayloadHistory.Past B f hf
    (BlockProgram.layout B (terminalOperands G 2).val X.positions T)
    (CompiledResident.payload B f hf (terminalOperands G 2) X.positions T n)
    (executeLevels B f hf T hT X z) calendar)
  (entry : TerminalProgram.VertexEntry (w := G.w) B f hf T hT X z
    (BlockProgram.layout B (terminalOperands G 2).val X.positions T) table baseBits laneBits
    (terminalOperands G) calendar reference bits)
  (pack : VertexPacked G (BlockProgram.layout B (terminalOperands G 2).val X.positions T)
    B.recordLimit (TraversalRoles.selected B f hf T hT X z)
    (StateExecution.finalState (B.execute f hf T hT X) z).totalWidth)
  (frame : LinkedVertexMemory G reference ord m)
  (width : MapConstants.widthThreshold B.shrink ≤ G.w)

variable (fits : ∀ x : ShrinkRoleDirectory.ShrinkSite (executeLevels B f hf T hT X z),
  ∀ m, canonicalFits B x.occurrence.i x.occurrence.state x.occurrence.selection (w := G.w)
    (Fintype.card B.Entry) n
    (endAddress (BlockProgram.layout B (terminalOperands G 2).val X.positions T) +
      words B.recordLimit (selectedLayers B f hf T hT X z))
    (layerBase B.recordLimit
      (endAddress (BlockProgram.layout B (terminalOperands G 2).val X.positions T))
      (TraversalRoles.selected B f hf T hT X z) x.val.1.val) limit m)
variable (x : ShrinkRoleDirectory.ShrinkSite (executeLevels B f hf T hT X z))
local notation "physical" => physicalSiteBank B f hf hT X z history entry pack frame width fits x

attribute [local irreducible] executeLevels ShrinkRoleDirectory.occurrence canonicalParent
  BlockProgram.layout BlockSchedule.Templates.execute StateExecution.finalState
include budget in
theorem physical_rates (node : Word G.w) (s : Scratch G.w n) (bs tail : List Bool)
    (body : VisitPath G.w n)
    (hit : (canonicalParent physical order f hf).read node s bs = some (body, tail)) :
    countProbes body.trace + 1 ≤ RatedRoles.scan B order * (n.log2 + 1)^1 ∧
      body.trace.length + 9 ≤ n^43 := by
  have wire := budget.old_width f hf hT z x.val.1
  have eqn := congrArg (fun v : SelectedLevel B f hf => v.input.maxWireWidth) x.occurrence.selected
  have typed : x.occurrence.state.maxWireWidth ≤ n := eqn.symm.le.trans wire
  obtain ⟨probes, ticks⟩ := canonicalParent_rates physical order f hf node rfl s bs tail body
    budget.rate (budget.later f hf hT z x.val.1) typed hit
  rw [pow_one]
  exact ⟨probes.trans (Nat.mul_le_mul_right _ (RatedRoles.role_le B order .shrink)), ticks⟩

include budget in
theorem physical_ordinal_cost (offset node : Word G.w) (s : Scratch G.w n) (bs tail : List Bool)
    (body : VisitPath G.w n)
    (hit : (canonicalParent physical order f hf).read node s bs = some (body, tail)) :
    ordinalJobCost n 1 (RatedRoles.scan B order) (dispatchJob m offset node s body) := by
  have h := physical_rates B f hf hT X z order budget history entry pack frame width fits x
    node s bs tail body hit
  exact ShrinkNodeCost.dispatched_ordinal_cost m offset node s body
    (by simpa only [pow_one] using h.1) h.2

end PairSimulation.ShrinkRole

end

end VPVNP
end Computability
end OAI
