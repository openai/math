import OAI.Computability.BorderVNP.FiniteEvaluatorReportStart
import OAI.Computability.BorderVNP.FiniteEvaluatorTaskMatrices

/-! # Finite field matrices of native report returns

Flattening the actual chronological guesses bijects the report preparer's
returning histories with the tapes of the declared length. Splitting at the
owned-cell boundaries gives one bit-major field matrix per cell.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Reports

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalResidueRAM TeamRAM
open TaskReadback (ReportTape Matrices)
open private rebit_inputs bits_rebit from OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReportsInverse

variable {w : ℕ} {pub : Arg → Word w} {m : Memory w} {l : Layout} {rows : List Row}
variable (start : Start pub m l rows) (mac : TeamOpcode.Macros w 8) (s : Bank w)
local notation "Hist" => Returns prepareReports pub mac s m

include start

private theorem cover (x : Hist) :
    let bs := x.val.1.flatMap Event.choices
    bs.length = capacity rows ∧ TraceOK x.val.1 bs x.val.1.length ∧
      traceCost x.val.1 ≤ setup.slots+ticks rows ∧ readings x.val.2.2 = image l (rebit rows bs) (readings m) :=
  prepare_cover pub mac s m l rows start.ptr start.seed start.frame start.control start.endHeaders
    start.headers start.rooms start.apart x.property

/-- Recover the chronological report guesses from a native return. Their length
is fixed by the owned-cell headers, including when the directory is empty. -/
def Start.returnTape (x : Hist) : ReportTape rows := ⟨_,(cover start mac s x).1⟩

private theorem bijective : Function.Bijective (start.returnTape mac s) := by
  constructor
  · intro x y eq
    obtain ⟨trace,bank,mem⟩ := prepare_unique x.property y.property (congrArg Subtype.val eq)
    exact Subtype.ext (Prod.ext trace (Prod.ext bank mem))
  · intro tape
    have len := rebit_length rows tape.val
    have input := rebit_inputs l l.headers rows (readings m) tape.val tape.property.symm.le
      start.headers start.rooms start.apart
    obtain ⟨es,t,mt,run,tr,_,_⟩ := prepare_run pub mac s m l (rebit rows tape.val)
      start.ptr (len ▸ start.seed) start.frame start.control (len ▸ start.endHeaders) input
    refine ⟨⟨(es,t,mt),run⟩,Subtype.ext ?_⟩
    change es.flatMap Event.choices = tape.val
    rw [tr.2.1,bits_rebit,List.take_of_length_le tape.property.le]

/-- Each tape of the physical length gives exactly one complete native return. -/
noncomputable def Start.tapeEquiv : ReportTape rows ≃ Hist :=
  (Equiv.ofBijective _ (bijective start mac s)).symm

variable (F : Type*) [Fintype F] (fields : l.scalars=Fintype.card F)

include fields

/-- Every owned header reserves all binary places of all the field labels. -/
theorem Start.bit_length (i : Fin rows.length) : rows[i].bits.length=l.digits*Fintype.card F := by
  simpa only [fields,Nat.mul_comm] using (start.rooms i).2.2.2.2

/-- All complete native returns, indexed by a bit-major field matrix at every
owned global cell. The return contains the chronological events, final bank
and final memory. -/
noncomputable def Start.matrixEquiv : Matrices F l.digits rows ≃ Hist :=
  (TaskReadback.matrixEquiv F l.digits rows (start.bit_length F fields)).trans (start.tapeEquiv mac s)

/-- The trace has exactly the matrix tape's choices, positive signs and the
native time bound. The output memory is the full chronological write image. -/
theorem Start.matrixEquiv_spec (c : Matrices F l.digits rows) :
    let x := start.matrixEquiv mac s F fields c
    let bs := (TaskReadback.matrixEquiv F l.digits rows (start.bit_length F fields) c).val
    TraceOK x.val.1 bs x.val.1.length ∧ traceCost x.val.1 ≤ setup.slots+ticks rows ∧
      readings x.val.2.2 = image l (rebit rows bs) (readings m) := by
  intro x bs
  have tape := (start.tapeEquiv mac s).symm_apply_apply
    (TaskReadback.matrixEquiv F l.digits rows (start.bit_length F fields) c)
  have eq : x.val.1.flatMap Event.choices = bs := congrArg Subtype.val tape
  simpa only [eq] using (cover start mac s x).2

/-- Read the matrix of any genuine report return directly from its own events,
in the chronological owned-row order seen by the field evaluator. -/
theorem Start.matrixEquiv_recover (x : Hist) (i : Fin rows.length) :
    ((rebit rows (x.val.1.flatMap Event.choices))[i.val]'(by simp)).bits =
      FiniteScalarRounds.stream F ((start.matrixEquiv mac s F fields).symm x i) := by
  let c := (start.matrixEquiv mac s F fields).symm x
  have eq := (start.matrixEquiv_spec mac s F fields c).1.2.1
  simp only [c,Equiv.apply_symm_apply] at eq
  rw [eq]
  exact TaskReadback.matrixEquiv_read ..

end FiniteEvaluator.Reports

end BorderVNP
end Computability
end OAI
