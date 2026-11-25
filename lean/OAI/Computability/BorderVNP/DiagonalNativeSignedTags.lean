import OAI.Computability.BorderVNP.RoutingISASignedProgram
import OAI.Computability.BorderVNP.CubeISAOwnedStrictSideInverse
import OAI.Computability.BorderVNP.CubeISALocalRowFrame
import OAI.Computability.BorderVNP.DiagonalNativeExpansionValue
import OAI.Computability.BorderVNP.DiagonalNativeUnitStartup

/-! # The actual evaluation body and its ordinary memory probes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open BorderVNP.Cube BorderVNP.Cube.Tally VPVNP.BurstRAM

/-- The genuine residue-evaluation branch inside the fixed signed processor program. -/
noncomputable def signedBody {n b h K s : ℕ} (id : TableEntry n b h K s → ℕ) : Code :=
  evaluate epochPlacement (scheduleGroups n (selectorWidth n K h))
    (signedInputs id (TeamRows.ownedGroups n b h K s)) signedOccurrences

/-- The three startup fragments, broadcast and tag selection contain exactly the signed body. -/
theorem withStartup_signedBody {n b h K s : ℕ} (id : TableEntry n b h K s → ℕ) :
    withStartup (signedBody id) = signedProgram id := rfl

/-- Acceptance occurs at the end of the whole fixed evaluation body. -/
theorem signedBody_withoutAccept {n b h K s : ℕ} (id : TableEntry n b h K s → ℕ) :
    (signedBody id).withoutAccept = true := by
  have input := signedInputs_returns id (TeamRows.ownedGroups_returns n b h K s)
  simp only [signedBody,evaluate,Code.block,Code.withoutAccept,scheduleGroups_returns,input,
    show preparePins.withoutAccept = true by decide,show epochPlacement.withoutAccept = true by decide,
    show Packing.Directory.ISA.program.withoutAccept = true by decide,show route.withoutAccept = true by decide,
    show callOwnedCells.withoutAccept = true by decide,show signedOccurrences.withoutAccept = true by decide,
    show DiagonalTallyRAM.complete.withoutAccept = true by decide,show leadEntry.withoutAccept = true by decide,
    Bool.and_self]

/-- Every reported cube ID, materialization, counter initialization and occurrence scan is deterministic. -/
theorem signedOccurrences_deterministic : signedOccurrences.deterministic = true := by decide

private theorem header_native (n bits : ℕ) : (CubeHeaderInstall.install n bits).nativeOnly = true := by
  have rep (op : PrivateRAM.BinaryOp) (x y : Reg) (k : ℕ) :
      (CubeHeaderInstall.repeatOp op x y k).nativeOnly = true := by
    induction k <;> simp [CubeHeaderInstall.repeatOp,Code.nativeOnly, *]
  simp only [CubeHeaderInstall.install,CubeHeaderInstall.volumeCode,Code.nativeOnly,rep,
    show CubeHeaderInstall.setup.nativeOnly=true by decide,show HeaderInstall.width.nativeOnly=true by decide,
    show CubeHeaderInstall.nextWidth.nativeOnly=true by decide,
    show (Packing.Directory.ISA.pushWords CubeHeaderInstall.columns).nativeOnly=true by decide,Bool.and_self]

private theorem groups_native (n bits : ℕ) : (scheduleGroups n bits).nativeOnly = true := by
  simp only [scheduleGroups,Code.block,Code.nativeOnly,header_native,
    show LabelIndex.directoryProgram.nativeOnly = true by decide,show NativeIntervals.prepare.nativeOnly=true by decide,
    show CubePowers.install.nativeOnly=true by decide,show HeaderDecode.program.nativeOnly=true by decide,
    show CubeLengths.minimum.nativeOnly=true by decide,show GroupWeights.checkedSchedule.nativeOnly=true by decide,
    show CellBanks.install.nativeOnly=true by decide,show PairDirectory.directory.nativeOnly=true by decide,
    show Transmission.DataWriter.program.nativeOnly=true by decide,show SharedRows.program.nativeOnly=true by decide,
    Bool.and_self]

private theorem owned_native (n b h K s : ℕ) : (TeamRows.ownedGroups n b h K s).nativeOnly = true := by
  have strict := (LocalRow.strictChecked n b h K s).nativeOnly_of_unsigned (LocalRow.strictChecked_unsigned ..)
  have diag := (LocalRow.diagonalChecked n b h K s).nativeOnly_of_unsigned (LocalRow.diagonalChecked_unsigned ..)
  simp only [TeamRows.ownedGroups,TeamRows.scan,TeamRows.body,TeamRows.select,TeamRows.strictRole,TeamRows.diagonalRole,
    Code.block,Code.nativeOnly,OwnedStages.strictSide_nativeOnly,OwnedStages.diagonalSide,OwnedStages.singleStage_nativeOnly,
    strict,diag,Bool.and_self,Bool.true_and]
  rfl

/-- All preparations, even the binary selector and routing guesses, use no private bursts.
The only such bursts in the signed evaluator occur in the subsequent cell dispatcher. -/
theorem signedPrepare_nativeOnly {n b h K s : ℕ} (id : TableEntry n b h K s → ℕ) :
    (prepareExpansion epochPlacement (scheduleGroups n (selectorWidth n K h))
      (signedInputs id (TeamRows.ownedGroups n b h K s))).nativeOnly = true := by
  have constants := (CubeConstants.install id).nativeOnly_of_unsigned (CubeConstants.install_unsigned id).1
  simp only [prepareExpansion,signedInputs,signedInputPrefix,List.cons_append,List.nil_append,Code.block,Code.nativeOnly,groups_native,constants,owned_native,
    show epochPlacement.nativeOnly = true by decide,show Packing.Directory.ISA.program.nativeOnly=true by decide,
    show route.nativeOnly=true by decide,show Padding.verify.nativeOnly=true by decide,
    show HostScatter.program.nativeOnly=true by decide,show Packing.BundleDirectory.program.nativeOnly=true by decide,
    show CellControlRows.program.nativeOnly=true by decide,show DiagonalTallyCellReports.prepareCellReports.nativeOnly=true by decide,
    show FragmentRows.program.nativeOnly=true by decide,show FragmentBucket.program.nativeOnly=true by decide,
    show TypedTaskBuilder.program.nativeOnly=true by decide,show CellPacket.Supplement.Batch.entry.nativeOnly=true by decide,
    show SparseExterior.prepare.nativeOnly=true by decide,
    show TypedBatch.entry.nativeOnly=true by decide,Bool.and_self]

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
