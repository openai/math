import OAI.Computability.BorderVNP.FiniteEvaluatorPublicPhase
import OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReports
import OAI.Computability.BorderVNP.FiniteEvaluatorCells
import OAI.Computability.BorderVNP.FiniteEvaluatorCubePacket
import OAI.Computability.BorderVNP.FiniteProfileContinuation

/-! # The closed word-RAM evaluator for the finite-field diagonal

The positive branch reconstructs the packed field network and checks the
physical cube declaration, routed bits and host work. Its owned-cell calls
return the signed validator factors and finite-field count products. Each
owned cube vertex contributes the scalar encoded by its selected entry.
The unit branch and the finite 81-word initialization use the same program.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open VPVNP.BurstRAM RoutingISA BorderVNP.Cube BorderVNP.Cube.Tally

variable {n b h K s : ℕ} {F : Type*} [Fintype F]

/-- The real task builder and supplemental typed-geometry writer follow
the finite bit-major report guesser. Empty supplement rows carry the
original stored field-ID count operands. -/
def prepareTasks : Code := .block [
  prepareReports, TypedTaskBuilder.program, CellPacket.Supplement.Batch.entry]

/-- The chronological private field output phase at the supplied prepared memory. -/
def privateReturns : Code := .seq Cells.code CubePacket.code

/-- The continuation at the end of the decoded profile and private-site placement. -/
noncomputable def afterPlacement (table : TableEntry n b h K s → F) : Code := .seq
  (.block [Packing.Directory.ISA.program,Evaluator.scheduleGroups n (selectorWidth n K h),Evaluator.route])
  (.seq (openCells table) (.seq prepareTasks privateReturns))

/-- The positive field branch with its real pin, epoch, route, owned table
and cube calls. The true cube table is the only input to this fixed code. -/
noncomputable def positive (table : TableEntry n b h K s → F) : Code :=
  .seq preparePins (.seq Evaluator.epochPlacement (afterPlacement table))

/-- Install the finite literal and extended frame, check the copied
physical broadcast, then dispatch to the actual unit or field evaluator. -/
noncomputable def program (table : TableEntry n b h K s → F) : Code :=
  FiniteDiagonal.dispatchTable FiniteDiagonal.wideStartup (positive table)

/-- The wide-startup profile correspondence applies at the true assembled
positive branch, with exactly its physical suffix. -/
theorem positive_eq_placed (table : TableEntry n b h K s → F) :
    positive table = FiniteDiagonal.placedBody PrivatePlacement.program (afterPlacement table) := rfl

private theorem routing_returns (n K h : ℕ) :
    (Code.block [Packing.Directory.ISA.program,Evaluator.scheduleGroups n (selectorWidth n K h),Evaluator.route]).withoutAccept = true := by
  have ok := publicPhase_returns n K h
  simpa only [publicPhase,Code.block,Code.withoutAccept,show preparePins.withoutAccept=true by decide,
    show Evaluator.epochPlacement.withoutAccept=true by decide,Bool.true_and] using ok

/-- All positive instructions fall through to the unique final accept. -/
theorem positive_returns (table : TableEntry n b h K s → F) : (positive table).withoutAccept = true := by
  have rt := routing_returns n K h
  simp only [positive,afterPlacement,Code.withoutAccept,rt,openCells_returns,
    show preparePins.withoutAccept=true by decide,show Evaluator.epochPlacement.withoutAccept=true by decide,
    show prepareTasks.withoutAccept=true by decide,show privateReturns.withoutAccept=true by decide,Bool.and_self]

/-- At the fetched native table, acceptance is exactly a genuine execution
of the complete concrete evaluator with its precise consumed choice tape. -/
theorem program_execute_iff (table : TableEntry n b h K s → F) {w : ℕ}
    {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8} {bank : Bank w} {m bits es} :
    TeamRAM.execute ((program table).program.fetch pub macros) ⟨0,bank⟩ m bits = some es ↔
      (∃ t mt, Runs pub macros (program table) bank m es t mt) ∧ es.map TeamRAM.Event.choices = bits :=
  Code.execute_iff_runs (FiniteDiagonal.dispatchTable_withoutAccept
    (by decide : FiniteDiagonal.wideStartup.withoutAccept = true) (positive_returns table))

end FiniteEvaluator

end BorderVNP
end Computability
end OAI
