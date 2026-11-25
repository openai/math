import OAI.Computability.BorderVNP.FiniteEvaluatorControlReportMatrix

/-! # Native finite matrices at the allocated owned cells -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Reports

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalTallyAllocation DiagonalResidueRAM

/-- The true scalar report start and receiving banks at the output of the
control publisher, including any unused global cell reservations. -/
structure Directory {w : ℕ} (pub : Arg → Word w) (m : Memory w) (pre : BeforeTasks) (banks : CellBanks.Layout)
    (ctl : CellControlRows.Layout) (source : ℕ → ℕ) (scalars digits : ℕ) : Prop where
  start : Start pub m (allocatedLayout pre ctl.frame ctl.control scalars digits) (controlRows ctl source scalars digits)
  inBank : ∀ i : Fin (controlRows ctl source scalars digits).length, (controlRows ctl source scalars digits)[i].InBank banks
  cells : banks.cells ≤ pre.bound.cells
  before : banks.bankStart+banks.cells*banks.stride ≤ pre.start

variable {w scalars digits : ℕ} {pub : Arg → Word w} {m : Memory w} {pre : BeforeTasks} {banks : CellBanks.Layout}
variable {ctl : CellControlRows.Layout} {source : ℕ → ℕ} {s : Bank w} {mac : TeamOpcode.Macros w 8}
variable (d : Directory pub m pre banks ctl source scalars digits) (F : Type*) [Fintype F] (fields : scalars=Fintype.card F)
local notation "rows" => controlRows ctl source scalars digits
local notation "hist" => Returns prepareReports pub mac s m

/-- All native finite report returns are the actual chronological bit-major
matrices. Each returned cell records the exact public tail length, both cleared
counters, and the bit at every allocated scalar address. -/
theorem Directory.matrix_returns :
    let E := d.start.matrixEquiv mac s F fields
    (∀ x : hist, let values := E.symm x
      TraceOK x.val.1 ((TaskReadback.matrixEquiv F digits (rows) (d.start.bit_length F fields)) values).val x.val.1.length ∧
        traceCost x.val.1 ≤ setup.slots+ticks (rows) ∧
        ∀ i : Fin (rows).length,
          ((rebit (rows) (x.val.1.flatMap TeamRAM.Event.choices))[i.val]'(by simp)).bits = FiniteScalarRounds.stream F (values i)) ∧
    (∀ (x : hist) (i : Fin (rows).length), let mt := readings x.val.2.2
      let r := rows[i]
      mt (pre.tailWidths+r.number)=digits*Fintype.card F ∧ mt (pre.counters+2*r.number)=0 ∧
        mt (pre.counters+2*r.number+1)=0 ∧
          ∀ v k, mt (r.start+(finProdFinEquiv (k,v)).val)=((E.symm x) i v k).toNat) := by
  intro E
  constructor
  · intro x values
    have result := d.start.matrixEquiv_spec mac s F fields values
    have he : d.start.matrixEquiv mac s F fields values=x := Equiv.apply_symm_apply E x
    simp only [he] at result
    exact ⟨result.1,result.2.1,fun i => d.start.matrixEquiv_recover mac s F fields x i⟩
  · exact control_matrix_readback d.start d.inBank d.cells d.before F fields

include d

/-- An arbitrary report return retains the whole primary, geometry and owner
region below the receiving banks, including owners of other teams. -/
theorem Directory.low (x : hist) (a : ℕ) (ha : a < banks.bankStart) :
    readings x.val.2.2 a=readings m a := control_matrix_low d.start d.inBank d.before x a ha

/-- The six native header words and every later reserved directory word survive
the scalar report return. -/
theorem Directory.directory_word (x : hist) (a : ℕ) (ha : pre.four ≤ a) :
    readings x.val.2.2 a=readings m a := control_matrix_directory d.start d.inBank d.cells d.before x a ha

end FiniteEvaluator.Reports

end BorderVNP
end Computability
end OAI
