import OAI.Computability.BorderVNP.RoutingISASignedProgram
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeWord

/-! # Shared geometry and scalar packet preparation of the finite-field evaluator

The positive branch resolves the original pins and public adaptive profile,
chooses the packet grouping, and performs real two-hop transmission. Each
team then installs the finite scalar words, checks its own selected packet
and singleton rows, and scatters the delivered ends into the owned host cells.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open VPVNP.BurstRAM RoutingISA BorderVNP.Cube BorderVNP.Cube.Tally
open private header_returns from OAI.Computability.BorderVNP.RoutingISASignedAssembly

variable {n b h K s : ℕ} {F : Type*} [Fintype F]

/-- Resolve the checked profile and pins, schedule the selected groups, and
perform actual shared, padded, and relayed bit transfers. -/
def publicPhase (n K h : ℕ) : Code := .block [
  preparePins, Evaluator.epochPlacement, Packing.Directory.ISA.program,
  Evaluator.scheduleGroups n (selectorWidth n K h), Evaluator.route]

/-- Real instructions from the completed transfers to the physical task
directory, with one fixed scalar lookup word per cube table position. -/
noncomputable def openCells (table : TableEntry n b h K s → F) : Code := .block [
  CubeConstants.install (fun e => CubeWord.encode (table e)), TeamRows.ownedGroups n b h K s,
  Padding.verify, HostScatter.program, Packing.BundleDirectory.program, CellControlRows.program]

/-- The public stages return to the next instruction in the enclosing finite evaluator. -/
theorem publicPhase_returns (n K h : ℕ) : (publicPhase n K h).withoutAccept = true := by
  simp only [publicPhase,Evaluator.epochPlacement,Evaluator.scheduleGroups,Evaluator.route,Code.block,Code.withoutAccept,
    header_returns,
    show preparePins.withoutAccept=true by decide,show GeometryAdvice.reconstruct.withoutAccept=true by decide,
    show PrivatePlacement.program.withoutAccept=true by decide,show Packing.Directory.ISA.program.withoutAccept=true by decide,
    show LabelIndex.directoryProgram.withoutAccept=true by decide,show NativeIntervals.prepare.withoutAccept=true by decide,
    show CubePowers.install.withoutAccept=true by decide,show HeaderDecode.program.withoutAccept=true by decide,
    show CubeLengths.minimum.withoutAccept=true by decide,show GroupWeights.checkedSchedule.withoutAccept=true by decide,
    show CellBanks.install.withoutAccept=true by decide,show PairDirectory.directory.withoutAccept=true by decide,
    show Transmission.DataWriter.program.withoutAccept=true by decide,show SharedRows.program.withoutAccept=true by decide,
    show scheduleTable.withoutAccept=true by decide,show checkPadding.withoutAccept=true by decide,
    show checkRelays.withoutAccept=true by decide,show transmitRanges.withoutAccept=true by decide,Bool.and_self]

/-- The cell-input producer reaches its continuation even for a zero-valued
scalar at an otherwise valid cube table position. -/
theorem openCells_returns (table : TableEntry n b h K s → F) : (openCells table).withoutAccept = true := by
  simp only [openCells,Code.block,Code.withoutAccept,(CubeConstants.install_unsigned _).2,TeamRows.ownedGroups_returns,
    show Padding.verify.withoutAccept=true by decide,show HostScatter.program.withoutAccept=true by decide,
    show Packing.BundleDirectory.program.withoutAccept=true by decide,show CellControlRows.program.withoutAccept=true by decide,
    Bool.and_self]

end FiniteEvaluator

end BorderVNP
end Computability
end OAI
