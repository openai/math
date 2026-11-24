import OAI.Computability.VPVNP.PairRefreshSelectedParser
import OAI.Computability.VPVNP.PairRefreshHookSelectedGuardLayout

/-! # Published guard layouts of chronological refresh rows -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.SelectedRows

open BurstRAM Compression CompressorRecords DescriptorSpace LocalHistory TraversalRows TraversalRoles
open TerminalProgram LiveProgram PairStages.Group.Auxiliary

variable {k K : Type} [_root_.Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → K) (hf : B.IsSolution f)
    (G : PairStages.Group) (n hist : ℕ) {l : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ l)
    (X : State (S.degreeExponent 0) l) (z : (B.execute f hf T hT X).Choices)

local notation "pub" => terminalOperands G
local notation "passes" => executeLevels B f hf T hT X z
local notation "L" => BlockProgram.layout B (Fin.val (pub 2)) X.positions T
local notation "first" => TaggedLayer.mk (leafLayer (siteOrder X)) Role.cursor
local notation "tags" => selected B f hf T hT X z
local notation "width" => State.totalWidth (StateExecution.finalState (B.execute f hf T hT X) z)
local notation "size" => tagWords B.recordLimit (tags)

variable (room : Rooms n hist G.w (terminalOperands G 2).val X.positions T
    ⟨leafLayer (siteOrder X), .cursor⟩ (executeLevels B f hf T hT X z))
local notation "site" => rowSite n hist G.w (Fin.val (pub 2)) X.positions T (width)
  (first) (passes) room

/-- Each actual selected refresh reads the two consecutive packed levels,
including at the last pass of a branch. -/
theorem guardLayout_at {baseBits laneBits ord : ℕ} {tab : Fin (L).shape.tables}
    {calendar reference m : Memory G.w} {bits : Fin (width) → Bool}
    (entry : VertexEntry B f hf T hT X z (L) tab baseBits laneBits pub calendar reference bits)
    (history : SelectedPayloadHistory.Past B f hf (L)
      (CompiledResident.payload B f hf (pub 2) X.positions T n) (passes) calendar)
    (packed : VertexPacked G (L) B.recordLimit (tags) (width))
    (frame : LinkedVertexMemory G reference ord m) (x : Row (passes)) :
    ∃ prev next, Site.GuardLayout B ((site) x) pub m (pub 2).val X.positions T prev next := by
  have stage := x.val.1.isLt
  have length := executeLevels_length B f hf T hT X z
  have live : (passes).length < (L).levels :=
    length.trans_lt (by rw [BlockProgram.actual_level_count]; omega)
  let prev : Fin (L).levels := ⟨x.val.1.val, stage.trans live⟩
  let next : Fin (L).levels := ⟨x.val.1.val + 1, (Nat.succ_le_of_lt stage).trans_lt live⟩
  refine ⟨prev, next, ?_⟩
  exact SelectedPublished.guard_at_site B f hf G (pub 2) X.positions T hT X z
    x.occurrence.state x.occurrence.choice (passes)[x.val.1].selector
    x.occurrence.port x.val.1 x.occurrence.selected entry history packed frame (room x)
    prev next rfl rfl

/-- The level locator's remaining scan only includes later physical levels. -/
theorem later_le (blocks : T ≤ n.log2 + 1) (x : Row (passes)) :
    ((site) x).later ≤ (S.steps + 1) * (n.log2 + 1) := by
  change (tags).length - 1 - (x.val.1.val + 1) ≤ _
  have count : (tags).length = (passes).length + 1 := by simp [selected]
  rw [count, Nat.add_sub_cancel]
  exact (Nat.sub_le ..).trans ((executeLevels_length B f hf T hT X z).trans
    (Nat.mul_le_mul_left _ blocks))

end PairSimulation.RefreshHook.SelectedRows

end VPVNP
end Computability
end OAI
