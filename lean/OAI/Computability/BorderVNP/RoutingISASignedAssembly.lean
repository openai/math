import OAI.Computability.BorderVNP.RoutingISAStageLink
import OAI.Computability.BorderVNP.FragmentRows
import OAI.Computability.BorderVNP.FragmentBucketProgram
import OAI.Computability.BorderVNP.CellSparseExteriorBatch
import OAI.Computability.BorderVNP.RoutingISACellBankProof
import OAI.Computability.BorderVNP.RoutingISACubePowers
import OAI.Computability.BorderVNP.RoutingISACubeConstantRun
import OAI.Computability.BorderVNP.PrivatePlacementPass
import OAI.Computability.BorderVNP.CubeLabelDirectoryProgram
import OAI.Computability.BorderVNP.CubeDirectedIntervalPrepare
import OAI.Computability.BorderVNP.CubeISAHeaderInstall
import OAI.Computability.BorderVNP.CubeISAHeaderDecode
import OAI.Computability.BorderVNP.CubeISALengthCode
import OAI.Computability.BorderVNP.CubeGroupWeightCheckedSchedule
import OAI.Computability.BorderVNP.CubeSharedRowsEmission
import OAI.Computability.BorderVNP.CubePairDirectory
import OAI.Computability.BorderVNP.CubeScatterPadding
import OAI.Computability.BorderVNP.CubeHostScatterProgram
import OAI.Computability.BorderVNP.PackedBundleDirectoryISA
import OAI.Computability.BorderVNP.DiagonalTallyReportDriver
import OAI.Computability.BorderVNP.RoutingISACellControlRows
import OAI.Computability.BorderVNP.RoutingISATypedTaskBuilder
import OAI.Computability.BorderVNP.RoutingISATypedBatchEntry
import OAI.Computability.BorderVNP.CellPacketSupplementalBatch
import OAI.Computability.BorderVNP.DiagonalTallyPacketResult
import OAI.Computability.BorderVNP.DiagonalTallyCubeSuffix
import OAI.Computability.BorderVNP.DiagonalTallyRAMAllocatedRun
import OAI.Computability.BorderVNP.DiagonalTallyAlign

/-!
# Signed evaluation using the public rows, routed bits and owned cell tasks

The public part computes its labels from the actual delivered rows, installs
and decodes the true broadcast declaration, checks its least coordinate and
its load budget, and constructs all destination banks and routed lists.
The local part checks the real packet and singleton padding, writes the
original cable ends to the host cells, prepares their compact private tasks,
and reads only the accepted report and packet bits into the residue tally.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally

/-- Reconstruct the publicly encoded epoch and determine each private
description's concrete slot in its final receiving cell. -/
def epochPlacement : Code := .seq GeometryAdvice.reconstruct PrivatePlacement.program

/-- Complete public group scheduling, followed by the physical literal and
shared-range output tables consumed by `route`. The selector code width
and dimension are fixed parameters of the cube identity. -/
def scheduleGroups (n selectorBits : ℕ) : Code := .block [
  LabelIndex.directoryProgram, NativeIntervals.prepare, CubePowers.install,
  CubeHeaderInstall.install n selectorBits, HeaderDecode.program, CubeLengths.minimum,
  GroupWeights.checkedSchedule, CellBanks.install, PairDirectory.directory,
  Transmission.DataWriter.program, SharedRows.program]

/-- The native preparation before the last seven-word typed initializer. Every
true exterior, report, bucket and supplemental task operand is established here. -/
noncomputable def signedInputPrefix {n b h K s : ℕ} (id : TableEntry n b h K s → ℕ)
    (ownedGroups : Code) : List Code := [
  CubeConstants.install id, ownedGroups, Padding.verify, HostScatter.program, Packing.BundleDirectory.program,
  CellControlRows.program, DiagonalTallyCellReports.prepareCellReports, FragmentRows.program,
  FragmentBucket.program, TypedTaskBuilder.program, CellPacket.Supplement.Batch.entry,
  SparseExterior.prepare]

/-- Install the physical sparse inputs and publish the compact typed bursts for the
private calls. -/
noncomputable def signedInputs {n b h K s : ℕ} (id : TableEntry n b h K s → ℕ)
    (ownedGroups : Code) : Code := .block (signedInputPrefix id ownedGroups ++ [TypedBatch.entry])

/-- The typed initializer starts from exactly the state produced by the fragment,
supplement and sparse exterior writers. The split preserves every actual event. -/
theorem signedInputs_split {w n b h K s : ℕ} (id : TableEntry n b h K s → ℕ) (ownedGroups : Code)
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {bank mem es z mz} :
    Runs pub mac (signedInputs id ownedGroups) bank mem es z mz ↔
      Runs pub mac (.seq (.block (signedInputPrefix id ownedGroups)) TypedBatch.entry) bank mem es z mz :=
  Runs.block_append_iff (a := signedInputPrefix id ownedGroups) (b := [TypedBatch.entry])
    (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)

/-- After the private calls, derive the actual cube position IDs, append
those increments, align the counters at a length-only address, allocate
the counter arrays, materialize all occurrences
and initialize the fresh counters. `evaluate` next runs the fixed tally
aggregation and invokes the matrix entry reader on team zero. -/
def signedOccurrences : Code := .block [
  DiagonalTallyPacketEmit.producePacketIDs, DiagonalTallyCubeSuffix.appendCubeOperands,
  DiagonalTallyRAM.alignTallies, DiagonalTallyRAM.allocateTallies, DiagonalTallyRAM.prepareTallies]

/-- Assemble the signed evaluator from its fixed cube format and the code
scanning assigned packet and singleton blocks on each owned group. -/
noncomputable def signedAssembly {n b h K s : ℕ} (id : TableEntry n b h K s → ℕ)
    (ownedGroups : Code) : Code :=
  assemble ExtendedFrame.install epochPlacement (scheduleGroups n (selectorWidth n K h))
    (signedInputs id ownedGroups) signedOccurrences

private theorem header_returns (n bits : ℕ) : (CubeHeaderInstall.install n bits).withoutAccept = true := by
  have rep (op : VPVNP.BurstRAM.PrivateRAM.BinaryOp) (x y : Reg) (k : ℕ) :
      (CubeHeaderInstall.repeatOp op x y k).withoutAccept = true := by
    induction k <;> simp [CubeHeaderInstall.repeatOp,Code.withoutAccept, *]
  simp only [CubeHeaderInstall.install,CubeHeaderInstall.volumeCode,Code.withoutAccept,
    rep,show CubeHeaderInstall.setup.withoutAccept = true by decide,
    show HeaderInstall.width.withoutAccept = true by decide,
    show CubeHeaderInstall.nextWidth.withoutAccept = true by decide,
    show (Packing.Directory.ISA.pushWords CubeHeaderInstall.columns).withoutAccept = true by decide,Bool.and_self]

/-- The entire schedule returns to its caller on each admitted group table. -/
theorem scheduleGroups_returns (n bits : ℕ) : (scheduleGroups n bits).withoutAccept=true := by
  simp only [scheduleGroups,Code.block,Code.withoutAccept,header_returns,
    show LabelIndex.directoryProgram.withoutAccept=true by decide,
    show NativeIntervals.prepare.withoutAccept=true by decide,show CubePowers.install.withoutAccept=true by decide,
    show HeaderDecode.program.withoutAccept=true by decide,show CubeLengths.minimum.withoutAccept=true by decide,
    show GroupWeights.checkedSchedule.withoutAccept=true by decide,show CellBanks.install.withoutAccept=true by decide,
    show PairDirectory.directory.withoutAccept=true by decide,show Transmission.DataWriter.program.withoutAccept=true by decide,
    show SharedRows.program.withoutAccept=true by decide,Bool.and_self]

/-- The compact cell inputs and their reported counts are prepared before private dispatch. -/
theorem signedInputs_returns {n b h K s : ℕ} (id : TableEntry n b h K s → ℕ) {ownedGroups : Code}
  (hg : ownedGroups.withoutAccept = true) : (signedInputs id ownedGroups).withoutAccept=true := by
  simp only [signedInputs,signedInputPrefix,List.cons_append,List.nil_append,Code.block,Code.withoutAccept,(CubeConstants.install_unsigned id).2,hg,
    show Packing.BundleDirectory.program.withoutAccept=true by decide,
    show DiagonalTallyCellReports.prepareCellReports.withoutAccept=true by decide,
    show Padding.verify.withoutAccept=true by decide,show HostScatter.program.withoutAccept=true by decide,
    show CellControlRows.program.withoutAccept=true by decide,show TypedTaskBuilder.program.withoutAccept=true by decide,
    show CellPacket.Supplement.Batch.entry.withoutAccept=true by decide,show TypedBatch.entry.withoutAccept=true by decide,
    show FragmentRows.program.withoutAccept=true by decide,show FragmentBucket.program.withoutAccept=true by decide,
    show SparseExterior.prepare.withoutAccept=true by decide,
    Bool.and_self]

/-- The native table accepts at its final instruction exactly when all the
linked scans return normally on the actual memory and choice tape. -/
theorem signedAssembly_execute_iff {w n b h K s : ℕ} (id : TableEntry n b h K s → ℕ)
    {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8} {ownedGroups : Code}
    (hg : ownedGroups.withoutAccept=true) {bank : Bank w} {m bits es} :
    let c := signedAssembly id ownedGroups
    TeamRAM.execute (c.program.fetch pub macros) ⟨0,bank⟩ m bits = some es ↔
      (∃ t mt, Runs pub macros c bank m es t mt) ∧ es.map TeamRAM.Event.choices = bits := by
  exact execute_iff (by decide) (by decide) (scheduleGroups_returns ..) (signedInputs_returns id hg) (by decide)

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
