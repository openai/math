import OAI.Computability.BorderVNP.DiagonalTallyReportBatch

/-! # Sparse total native charge over the owning team's true cells -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open RoutingISA DiagonalResidueRAM

/-- Actual original-site header and one-copy weighted metadata volume. -/
def teamOriginal {l : ReportLayout} (cs : List (ReportCell l)) :=
  (cs.map fun c => originalFields c.bundles).sum

/-- Actual number of expanded marked occurrences among this owner's cells. -/
def teamWeighted {l : ReportLayout} (cs : List (ReportCell l)) :=
  (cs.map fun c => weightedCopies c.bundles).sum

/-- All loop guards, header decoding, supplemental rows, and sampled bits are
charged to the owned cells and genuine metadata. The multiplicity term charges
only the physically listed marked positions. -/
theorem cellTicks_sparse {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor) :
    cellTicks cs q ≤ 1+(79+105*l.gadgets+16*(l.gadgets*l.countWidth))*cs.length+
      129*teamOriginal cs*(l.fieldWidth+1)+131*teamWeighted cs := by
  induction cs generalizing q with
  | nil => simp [cellTicks,teamOriginal,teamWeighted]
  | cons c cs ih =>
    have step := c.sparse_cost q
    have tail := ih (c.after q)
    change 1+(c.prefixCost q+publishCell.slots+(6*c.bits.length+6))+cellTicks cs (c.after q) ≤ _
    simp only [teamOriginal,teamWeighted,List.map_cons,List.sum_cons,List.length_cons,Nat.mul_succ]
    unfold teamOriginal teamWeighted at tail
    nlinarith

/-- Uniform ordinary-tick bound for the complete native owner program, with no
work on unused staging capacity and no per-cell scan of the parameter vector. -/
theorem prepare_sparse_charge {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor) :
    prepareSetup.slots+cellTicks cs q+(writeFrame 32 60 61 35).slots ≤
      54+(79+105*l.gadgets+16*(l.gadgets*l.countWidth))*cs.length+
      129*teamOriginal cs*(l.fieldWidth+1)+131*teamWeighted cs := by
  have h := cellTicks_sparse cs q
  change 49+cellTicks cs q+4 ≤ _
  omega

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
