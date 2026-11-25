import OAI.Computability.BorderVNP.DiagonalSelectedRawWriterRoom
import OAI.Computability.BorderVNP.DiagonalSignedBundleBankRoom

/-! # Writer address bounds for the selected seven-word directory and signed packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Packing Packing.RoutingOutputs PackedHistoryCircuit.TerminalCells RoutingISA GeometryAdvice

/-- The appended output word count covers every routing operand, including
the control prefix read on the local dictionary branch. The same frontier
bounds every candidate and its full native cell stride. -/
theorem SelectedRawWriterRoom.located_writer_fields {ar : CubeArena.Layout} {dir : Directory.Layout}
    {w X next profile gates outputs field : ℕ}
    (room : SelectedRawWriterRoom ar dir w X next profile gates outputs field)
    (pack depth : ℕ) (words : outputs=signedGridOutputCount ar.cables ar.cells dir.entries (dir.teams*dir.sites) 37 pack+
      (2^depth+2^depth)) (short : dir.description≤dir.literal) :
    let origin := Allocation.dest (next+7*dir.candidates) profile gates outputs field
    let control := controlsBase origin ar.cables ar.cells dir.entries (dir.teams*dir.sites)
    let table := bases origin ar.cables ar.cells dir.entries
    control+37≤ar.header.header ∧
      Directory.ISA.wordBound (Directory.ISA.placementBound dir table.privatePairs table.livePairs ar.cellStride)<2^w := by
  intro origin control table
  have prefixSize : ar.cables*3+count ar.cables ar.cells dir.entries (dir.teams*dir.sites)+
      (ar.cells+(dir.entries+ar.cells)+37)≤outputs := by
    rw [words]
    unfold signedGridOutputCount
    have positive : 0<(2:ℕ)^depth := by positivity
    omega
  have frontier : control+37≤origin+outputs := by
    dsimp only [control,controlsBase,bases,count] at *
    omega
  have top := congrArg CubeHeaderInstall.Inputs.header room.template
  change ar.header.header=Allocation.stop (next+7*dir.candidates) profile gates outputs field w at top
  refine ⟨frontier.trans ?_,room.placement short prefixSize _ le_rfl⟩
  rw [top]
  change origin+outputs ≤ origin+outputs+_+_
  omega

end Diagonal

end BorderVNP
end Computability
end OAI
