import OAI.Computability.BorderVNP.FiniteEvaluatorProgram
import OAI.Computability.BorderVNP.FragmentRows
import OAI.Computability.BorderVNP.RoutingISASignedProgram

/-! # Closed finite-field evaluator with the real sparse exterior encoder -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open VPVNP.BurstRAM RoutingISA BorderVNP.Cube BorderVNP.Cube.Tally

variable {n b h K s : ℕ} {F : Type*} [Fintype F]

/-- The finite count guesser writes the real uncompressed chronological
report tail. Fragment collection and bucketing preserve occupied intervals.
After the typed task and supplemental geometry are installed, the sparse
encoder appends those true report bits to the compressed prefix and writes
the physical byte address and length consumed by slot zero. -/
def prepareSparseTasks : Code := .block [prepareReports,FragmentRows.program,FragmentBucket.program,
  TypedTaskBuilder.program,CellPacket.Supplement.Batch.entry,SparseExterior.prepare]

/-- The public task preparation matching the physical private decoder.
The sparse driver and every public instruction are fixed independently
of the site-dependent interval list. -/
def prepareTasksFor : Cells.Codec → Code
  | .dense => prepareTasks
  | .sparse _ => prepareSparseTasks

/-- True continuation after publication of the seven-word demands. -/
noncomputable def afterPublicationFor (table : TableEntry n b h K s → F) (codec : Cells.Codec) : Code := .seq
  (.seq (Evaluator.scheduleGroups n (selectorWidth n K h)) Evaluator.route)
  (.seq (openCells table) (.seq (prepareTasksFor codec) privateReturns))

/-- True continuation after the private history programs are placed. -/
noncomputable def afterPlacementFor (table : TableEntry n b h K s → F) (codec : Cells.Codec) : Code := .seq
  (.block [Packing.Directory.ISA.program,Evaluator.scheduleGroups n (selectorWidth n K h),Evaluator.route])
  (.seq (openCells table) (.seq (prepareTasksFor codec) privateReturns))

/-- Positive branch on the physically matched exterior encoding. -/
noncomputable def positiveFor (table : TableEntry n b h K s → F) (codec : Cells.Codec) : Code :=
  .seq preparePins (.seq Evaluator.epochPlacement (afterPlacementFor table codec))

/-- Concrete finite program, including its actual wide startup, branch
dispatch, native fragment producer, sparse packet encoder and field calls. -/
noncomputable def programFor (table : TableEntry n b h K s → F) (codec : Cells.Codec) : Code :=
  FiniteDiagonal.dispatchTable FiniteDiagonal.wideStartup (positiveFor table codec)

/-- The one sparse physical evaluator for all authentic interval data. -/
noncomputable def sparseProgram (table : TableEntry n b h K s → F) : Code :=
  programFor table (.sparse fun _ => ⟨0,[],[]⟩)

/-- Sparse metadata are used by the word-correctness proof only; the
assembled native code is identical for every legal private payload. -/
theorem sparseProgram_eq (table : TableEntry n b h K s → F) (fields : ℕ → SparseExterior.Field) :
    programFor table (.sparse fields) = sparseProgram table := rfl

/-- Every positive instruction of the real sparse program returns to the
common dispatcher. -/
theorem positiveFor_returns (table : TableEntry n b h K s → F) (codec : Cells.Codec) :
    (positiveFor table codec).withoutAccept = true := by
  cases codec with
  | dense => exact positive_returns table
  | sparse fields =>
    have sparse : prepareSparseTasks.withoutAccept = true := by decide
    have dense : prepareTasks.withoutAccept = true := by decide
    simpa only [positiveFor,afterPlacementFor,prepareTasksFor,positive,afterPlacement,Code.withoutAccept,sparse,dense]
      using positive_returns table

/-- Actual chronological execution on this table uses exactly the events
and choice blocks of its corresponding positive or unit branch. -/
theorem programFor_execute_iff (table : TableEntry n b h K s → F) (codec : Cells.Codec) {w : ℕ}
    {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8} {bank : Bank w} {m bits es} :
    TeamRAM.execute ((programFor table codec).program.fetch pub macros) ⟨0,bank⟩ m bits = some es ↔
      (∃ t mt, Runs pub macros (programFor table codec) bank m es t mt) ∧ es.map TeamRAM.Event.choices=bits :=
  Code.execute_iff_runs (FiniteDiagonal.dispatchTable_withoutAccept
    (by decide : FiniteDiagonal.wideStartup.withoutAccept=true) (positiveFor_returns table codec))

end FiniteEvaluator

end BorderVNP
end Computability
end OAI
