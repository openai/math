import OAI.Computability.BorderVNP.DiagonalFrozenPaddingControls
import OAI.Computability.BorderVNP.DiagonalSameReportVisits
import OAI.Computability.BorderVNP.DiagonalProposedReportSeedWords

/-! # The report allocation at the frame actually read by an owned team -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep
open FiniteEvaluator RoutingISA.Transmission DiagonalResidueRAM DiagonalTallyAllocation DiagonalTallyCellReports

/-- Transfer the observed directory seed to its semantic rows. The bank
uses the original frame word of this team, and the six-word headers are
read in the memory returned by its own control program. -/
theorem FrozenControlEntry.reportAllocationAtReturn
    {t : SignedTaskArena.Layout} {prog : OpenSuffix.Inputs} {frame ctl offsets w : ℕ}
    {supplied : Fin t.cube.cells → ℕ} {initial : ℕ → ℕ}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {regs : Bank w} {owned : Memory w}
    (entry : FrozenControlEntry t prog frame (pub 0).val ctl offsets w supplied initial (readings owned))
    (axis : Fin (t.cube.n+1))
    {layout semantic : ReportLayout} {cs : List (ReportCell layout)} {reported : List (ReportCell semantic)}
    (same : SameReportCells cs reported)
    (advance : Returns SignedPrep.controls pub mac regs owned)
    (_report : Returns prepareCellReports pub mac advance.val.2.1 advance.val.2.2)
    {cursor : ReportCursor} {description : ℕ}
    (seed : PreparedReportInput pub advance.val.2.2 cs cursor description)
    (alloc : ReportAllocation t.before t.after (t.cube.cellWriter frame ctl axis) layout cs cursor) :
    PreparedReportInput pub advance.val.2.2 reported cursor description ∧
      ReportAllocation t.before t.after (t.cube.cellWriter (pub 0).val ctl axis) semantic reported cursor ∧
      CellPacket.WordsAt (readings advance.val.2.2) semantic.headers (reported.flatMap ReportCell.headerWords) := by
  have nativeSeed := same.source_seed seed
  have nativeAllocation := same.source_allocation alloc
  exact ⟨nativeSeed,entry.frame.symm ▸ nativeAllocation,RoutingISA.Evaluator.SignedPrep.PreparedReportInput.physicalHeaders nativeSeed nativeAllocation⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
