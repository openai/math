import OAI.Computability.VPVNP.PairTerminalSiteDirectories

/-! # The shrinking locator on the current linked vertex memory -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalControllerInputs

open BurstRAM TraversalRoles
open private resident_data_frame from OAI.Computability.VPVNP.PairTerminalSiteDirectories

/-- Only the six terminal scalar words and the headers inside the
level interval need to be stable. The reference directories keep their
original word values when counters below the first level change. -/
theorem Resident.transfer_interval {w H first pitch offset cap base limit : ℕ}
    {pub : Fin 11 → Word w} {reference current : Memory w}
    {leaf : TaggedLayer} {ls : List (Fiber w)}
    (d : Resident pub reference H first pitch offset cap base leaf ls)
    (headers : ∀ j ≤ ls.length, first + j * pitch + 28 ≤ limit)
    (range : ∀ x, first ≤ x → x < limit → current x = reference x)
    (terminal : ∀ j ∈ terminalScalars, current (H + j) = reference (H + j)) :
    Resident pub current H first pitch offset cap base leaf ls := by
  apply resident_data_frame d terminal
  intro j hj o ho
  exact range _ (by omega) ((Nat.add_lt_add_left ho _).trans_le (headers j hj))

end PairSimulation.TraversalControllerInputs

namespace PairSimulation.TerminalProgram

open BurstRAM Compression CompressorRecords DescriptorSpace LocalHistory
open TraversalRows TraversalRoles TraversalControllerInputs LiveProgram PairStages.Group.Auxiliary
open scoped Fin.CommRing

variable {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
    {B : S.Templates} {f : B.Entry → A} {hf : B.IsSolution f} {lanes T : ℕ}
    {hT : T * S.laneBits ≤ lanes} {X : State (S.degreeExponent 0) lanes}
    {z : (B.execute f hf T hT X).Choices} {G : PairStages.Group} {positions : ℕ}

local notation "vs" => executeLevels B f hf T hT X z
local notation "ls" => selectedLayers B f hf T hT X z
local notation "tags" => selected B f hf T hT X z
local notation "pub" => terminalOperands G
local notation "layout" => BlockProgram.layout B (Fin.val (pub 2)) positions T
local notation "width" => State.totalWidth (StateExecution.finalState (B.execute f hf T hT X) z)

/-- The installed shrink handler uses the same directory family that the
calendar froze in the shared-bit reference memory. Its live locator reads
the headers in the later memory of this vertex. -/
theorem VertexEntry.shrinkLocator {baseBits laneBits ord : ℕ} {tab : Fin (layout).shape.tables}
    {calendar reference current : Memory G.w} {bits : Fin (width) → Bool}
    (entry : VertexEntry B f hf T hT X z (layout) tab baseBits laneBits (pub)
      calendar reference bits)
    (packed : VertexPacked G (layout) B.recordLimit (tags) (width))
    (later : LinkedVertexMemory G reference ord current) :
    ∃ ds : (i : Fin (vs).length) → LevelDirectory (vs)[i] reference (endAddress (layout)),
      Resident (pub) current (vertexHeader G).val (levelStart (layout) 0) (levelWords (layout))
        (words B.recordLimit (ls) + (width)) B.recordLimit (endAddress (layout))
        ⟨leafLayer (siteOrder X), .cursor⟩ (levelFibers (vs) ds) := by
  have live : (vs).length < (layout).levels := by
    rw [← TerminalBootstrap.selected_last_index, TerminalBootstrap.selected_prior_length,
      BlockProgram.actual_level_count, Nat.mul_comm T]
    omega
  obtain ⟨ds, _, resident⟩ := entry.boundedDirectories
  obtain ⟨range, terminal⟩ := packed.traversal_frames later
  refine ⟨ds, resident.transfer_interval (limit := endAddress (layout)) ?_ ?_ terminal⟩
  · intro j hj
    apply TraversalResidentHandoff.headers_before (layout) live (by change 28 ≤ 54; decide) j
    simpa only [levelFibers, List.length_ofFn] using hj
  · intro x lo hi
    exact range x (by simpa only [levelStart, Nat.zero_mul, Nat.add_zero] using lo) hi

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI
