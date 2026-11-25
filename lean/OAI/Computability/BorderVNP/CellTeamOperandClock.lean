import OAI.Computability.BorderVNP.CellTeamOccurrenceClock
import OAI.Computability.BorderVNP.DiagonalTallyRAMEvaluation
import OAI.Computability.BorderVNP.RoutingISACellControlProgram
import OAI.Computability.BorderVNP.RoutingISATypedTaskProgram

/-! # Exact input size of the true physically emitted tally descriptors -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open RoutingISA DiagonalTallyMaterialize DiagonalTallyOperandArray Cube.TeamRowClock

private theorem bundle_digits (bs : List ReportBundle) (q : ReportCursor) (ext : ℕ) :
    ((bundleOperands bs q ext).map (fun o => o.digits.length)).sum = weightedCopies bs := by
  induction bs generalizing q ext with
  | nil => simp [bundleOperands,weightedCopies]
  | cons b bs ih =>
    simp [bundleOperands,weightedCopies,List.map_ofFn,Function.comp_def,ReportBundle.operand,unaryOperand,ih]

/-- Each actual unary descriptor reads exactly one bit, and each count descriptor
reads its own complete width. This counts the materializer's dereferences. -/
theorem actual_operand_sizes {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor) :
    (cellOperands cs q).length = cs.length*l.gadgets+teamWeighted cs ∧
    ((cellOperands cs q).map (fun o => o.digits.length)).sum = cs.length*(l.gadgets*l.countWidth)+teamWeighted cs := by
  induction cs generalizing q with
  | nil => simp [cellOperands,teamWeighted]
  | cons c cs ih =>
    obtain ⟨rows,digits⟩ := ih (c.after q)
    simp only [cellOperands,List.length_append,ReportCell.operands,List.map_append,List.sum_append,rows,digits,
      List.length_ofFn,bundleOperands_length,bundle_digits,List.map_ofFn,Function.comp_def,Frame.countRow,
      Frame.countDigits,List.length_reverse,ReportCell.countFrame,List.length_cons,teamWeighted,
      List.map_cons,List.sum_cons]
    simp only [List.ofFn_const,List.sum_replicate,nsmul_eq_mul,Nat.cast_id,Nat.succ_mul]
    unfold teamWeighted at rows digits
    constructor <;> omega

/-- One true physical cube record adds one descriptor and one bit dereference to
the preceding owned-cell data. Relocating its data pointers does not alter these lengths. -/
theorem materialize_charge {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor)
    (vertices : ℕ) (record : Fin vertices → Operand) (cube : ∀ j, (record j).digits.length=1)
    (pub powers : ℕ) (countFields : cs.length*(l.gadgets+l.gadgets*l.countWidth) ≤ pub)
    (use : teamWeighted cs ≤ powers) :
    let os := cellOperands cs q ++ List.ofFn record
    DiagonalTallyMaterialize.setup.slots+21*os.length+8*(os.map (fun o => o.digits.length)).sum+1 ≤
      DiagonalTallyMaterialize.setup.slots+1+21*pub+29*(powers+vertices) := by
  intro os
  obtain ⟨rows,digits⟩ := actual_operand_sizes cs q
  have one : ((List.ofFn record).map (fun o => o.digits.length)).sum = vertices := by
    simp [List.map_ofFn,Function.comp_def,cube]
  dsimp only [os]
  rw [List.length_append,rows,List.length_ofFn,List.map_append,List.sum_append,digits,one]
  rw [Nat.mul_add] at countFields
  omega

/-- Exact common constants for the ordinary global control and task-row producers.
Both scan the global cell array once. -/
theorem header_task_charge (cells : ℕ) :
    CellControlRows.setup.slots+cells*(CellControlRows.body.slots+1)+1+CellControlRows.finish.slots+
      (TypedTaskBuilder.setup.slots+cells*(TypedTaskBuilder.body.slots+1)+2) ≤ 512*(cells+1) := by
  have a : CellControlRows.setup.slots+1+CellControlRows.finish.slots+TypedTaskBuilder.setup.slots+2 ≤ 512 := by decide
  have b : CellControlRows.body.slots+1+(TypedTaskBuilder.body.slots+1) ≤ 512 := by decide
  have h := Nat.mul_le_mul_left cells b
  rw [Nat.mul_add] at h
  omega

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
