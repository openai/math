import OAI.Computability.BorderVNP.FiniteEvaluatorOwnedReportRows
import OAI.Computability.BorderVNP.FiniteEvaluatorReportMatrixReadback

/-! # Scalar reports at the original controlled receive banks

Every native scalar-report return preserves the previously delivered input of
each owned cell. Its fresh matrix follows that prefix in the global cell's
allocated receive bank. Both the lower public words and the later four-word
and six-word directories survive the report stores.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Reports

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalTallyAllocation

variable {w scalars digits : ℕ} {ctl : CellControlRows.Layout} {source : ℕ → ℕ}
variable {pre : BeforeTasks} {banks : CellBanks.Layout} {pub : Arg → Word w} {m : Memory w}
variable {mac : TeamOpcode.Macros w 8} {s : Bank w}
local notation "rows" => controlRows ctl source scalars digits
local notation "l" => allocatedLayout pre ctl.frame ctl.control scalars digits
local notation "Hist" => Returns prepareReports pub mac s m
variable (start : Start pub m (allocatedLayout pre ctl.frame ctl.control scalars digits)
  (controlRows ctl source scalars digits))
variable (inBank : ∀ i : Fin (controlRows ctl source scalars digits).length,
  (controlRows ctl source scalars digits)[i].InBank banks)
variable (count : banks.cells ≤ pre.bound.cells) (before : banks.bankStart+banks.cells*banks.stride ≤ pre.start)

include inBank count before in
/-- Recover an arbitrary report return's field matrices at the true global
cell's allocated tail, zero counters, and bit-major receive addresses. -/
theorem control_matrix_readback (F : Type*) [Fintype F] (fields : scalars = Fintype.card F)
    (x : Hist) (i : Fin (rows).length) :
    let r := rows[i]
    let mt := readings x.val.2.2
    let c := (start.matrixEquiv mac s F fields).symm x
    mt (pre.tailWidths+r.number) = digits*Fintype.card F ∧ mt (pre.counters+2*r.number) = 0 ∧
      mt (pre.counters+2*r.number+1) = 0 ∧ ∀ v k, mt (r.start+(finProdFinEquiv (k,v)).val) = (c i v k).toNat := by
  let c := (start.matrixEquiv mac s F fields).symm x
  have separated : rows[i].Separated (l) := row_separated_le (inBank i) count before
  have later (j : Fin (rows).length) (lt : i < j) (a : ℕ) (hit : ¬ rows[i].Outside (l) a) : rows[j].Outside (l) a :=
    row_apart_le (inBank i) (inBank j) count before (fun eq => lt.ne (controlRow_injective eq)) a hit
  have seen := start.matrixEquiv_readback mac s F fields c i separated later
  simp only [c,Equiv.apply_symm_apply] at seen
  simpa only [allocatedLayout] using seen

include start inBank before in
/-- All the old canonical bits of this same globally owned cell remain in
its supplied bank, immediately before the newly appended field report. -/
theorem control_matrix_prefix (x : Hist) (i : Fin (rows).length) (j : ℕ) (inside : j < rows[i].canonical) :
    readings x.val.2.2 (rows[i].base+j) = readings m (rows[i].base+j) := by
  apply start.output_outside
  intro k
  exact supplied_outside_of_banks (inBank i) (inBank k) before
    (fun eq => congrArg (fun j : Fin (rows).length => rows[j]) (controlRow_injective eq)) inside

include start inBank before in
/-- All words below the original receive banks survive every possible native
report history, including the public frame, geometry and owner columns there. -/
theorem control_matrix_low (x : Hist) (a : ℕ) (low : a < banks.bankStart) : readings x.val.2.2 a = readings m a := by
  apply start.output_outside
  intro i
  have base := (inBank i).2.1
  have lo : banks.bankStart ≤ rows[i].base := by rw [base]; exact Nat.le_add_right ..
  have tail : pre.tailWidths = pre.start := rfl
  have counts : pre.start ≤ pre.counters := by
    simp only [BeforeTasks.counters,BeforeTasks.supplement,BeforeTasks.tailWidths]
    omega
  simp only [Row.Outside,Row.start,allocatedLayout]
  omega

include start inBank count before in
/-- The four-word and six-word control tables and all later addresses survive
the report pass even when the public cell reservation has unused entries. -/
theorem control_matrix_directory (x : Hist) (a : ℕ) (high : pre.four ≤ a) : readings x.val.2.2 a = readings m a :=
  start.output_outside x a (fun i => beyond_four_outside_le (inBank i) count before high)

end FiniteEvaluator.Reports

end BorderVNP
end Computability
end OAI
