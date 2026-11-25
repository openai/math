import OAI.Computability.BorderVNP.DiagonalTallyReportCellPrefix

/-! # Charging the native report preparation to its physical sparse input -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open RoutingISA DiagonalTallyOperandArray

/-- The one gadget block uses a single descriptor and one address vector per gadget. -/
theorem countWriter_cost (f : Frame) :
    f.cost .count=19+10*(f.gadgets*f.width)+105*f.gadgets := by
  unfold Frame.cost
  change 6+(f.gadgets*f.width*(6+3+1)+1)+5+(5*f.gadgets*(17+3+1)+1)+6=_
  ring

/-- The unary descriptor writer's cost is linear in the number of actual marked copies. -/
theorem unaryWriter_cost (f : Frame) : f.cost .unary=20+125*(f.marked*f.copies) := by
  unfold Frame.cost
  change 7+(f.marked*f.copies*(1+3+1)+1)+5+(5*(f.marked*f.copies)*(20+3+1)+1)+6=_
  ring

/-- The compact original-site scalar metadata costs one scan per bundle. Only the
marked positions incur the second, per-copy charge. -/
theorem ReportBundle.sparse_cost (b : ReportBundle) (l : ReportLayout) (q : LocalReportCursor) :
    b.cost l q ≤ 128*(1+b.positions.length)*(l.fieldWidth+1)+125*b.useCount := by
  have h := DiagonalTallyBits.ticks_le 1 l.fieldWidth
  have h' := DiagonalTallyBits.ticks_le (3*b.positions.length) l.fieldWidth
  unfold ReportBundle.cost
  rw [unaryWriter_cost]
  change 14+(5+DiagonalTallyBits.ticks 1 l.fieldWidth+3+
    DiagonalTallyBits.ticks (3*b.positions.length) l.fieldWidth+(28*b.positions.length+23)+
    (20+125*(b.positions.length*b.header.copies))+6) ≤
    128*(1+b.positions.length)*(l.fieldWidth+1)+125*(b.positions.length*b.header.copies)
  nlinarith [Nat.zero_le (b.positions.length*l.fieldWidth)]

/-- Number of weighted one-copy positions plus one header per genuine source bundle. -/
def originalFields (bs : List ReportBundle) := (bs.map (fun b => 1+b.positions.length)).sum

/-- Number of actual weighted copies, the only report work proportional to clone multiplicity. -/
def weightedCopies (bs : List ReportBundle) := (bs.map ReportBundle.useCount).sum

/-- Uniform bound on the actual retained-bundle loop, including its final guard. -/
theorem bundleTicks_sparse (l : ReportLayout) (bs : List ReportBundle) (q : LocalReportCursor) :
    bundleTicks l bs q ≤ 1+129*originalFields bs*(l.fieldWidth+1)+125*weightedCopies bs := by
  induction bs generalizing q with
  | nil => simp [bundleTicks,originalFields,weightedCopies]
  | cons b bs ih =>
    have step := b.sparse_cost l q
    have tail := ih (q.advance b)
    change 1+b.cost l q+bundleTicks l bs (q.advance b) ≤ _
    simp only [originalFields,weightedCopies,List.map_cons,List.sum_cons] at ⊢
    unfold originalFields weightedCopies at tail
    nlinarith [Nat.zero_le (b.positions.length*l.fieldWidth)]

/-- Cost of the whole per-cell prefix, counter publication and exact compact bit
sampling. The parameter count occurs only in addresses; no length-h array is visited here. -/
theorem ReportCell.sparse_cost {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) :
    c.prefixCost q + publishCell.slots + (6*c.bits.length+6) ≤
      78+105*l.gadgets+16*(l.gadgets*l.countWidth)+
      129*originalFields c.bundles*(l.fieldWidth+1)+131*weightedCopies c.bundles := by
  have hb := bundleTicks_sparse l c.bundles (c.localStart q)
  rw [ReportCell.prefixCost,countWriter_cost,c.bits_length]
  change 34+(19+10*(l.gadgets*l.countWidth)+105*l.gadgets)+
    bundleTicks l c.bundles (c.localStart q)+18+
    (6*(l.gadgets*l.countWidth+weightedCopies c.bundles)+6) ≤ _
  omega

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
