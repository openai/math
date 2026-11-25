import OAI.Hierarchy.DescentRegisteredResetSample
import OAI.Hierarchy.DescentNamedSheetReturnBill
import OAI.Hierarchy.DescentResetLookupTraffic

namespace OAI
/-! Six costs of the actual ranked and retained operand phase, expressed at its entry. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSixParty DescentStaticWordColumn DescentOperandFamilyBook
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "C" => (v).setup
local notation "place_" => (v).operandFloor b
local notation "L" => (v).rankBook ((v).linkedRankInputs u.sectors ((v).sheetsStart b)) b

def sheetPart (j : Fin 6) : ℕ :=
  ![(v).sheetLookups (v).receiver.candidates u.headerWork,
    ((L).clockBudget 7+7*(L).textBudget 7)+
      ((L).tailClock (v).receiver.capacity 7+7*(L).tailText (v).receiver.capacity 7),
    (v).controlRegisters.fee,
    (C).seven.invoice place_ w 7,
    (C).placement.invoice (C).signedFields 7,
    ((C).packets.lane ((C).placed place_) false).invoice+
      ((C).packets.lane ((C).placed place_) true).invoice] j

theorem sheet_parts : u.sheetBill=∑j,u.sheetPart j:=by
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,
    Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp only [sheetBill,sheetPart,ResetOutput.rowBill,ResetOutput.sheetLookups,
    DescentResetOperandSetup.Chart.setupInvoice,dictionaryCharge,Matrix.cons_val_zero,Matrix.cons_val_succ,
    ←u.sectors.count]
  ac_rfl

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

namespace Hierarchy.DescentSixParty.RegisteredReset.Sample
open DescentCompiler DescentDatedAddressBook PhysicalReset NativePitch Chronology
variable {F : Type} [Field F] {G : PoweredGadget F} {n d : ℕ} {board : NonlinearExpanders.Graph n d}
  {op : RotorSpec} {K : Parameters} {τ B h : ℕ} (a : Sample G board op K τ B h)
noncomputable section
def sheetCost (j : Fin 6) := a.inputs.sheetPart j*a.w

theorem sheets_paid (g : a.Geometry) : a.charges.sheets≤∑j,a.sheetCost j:=by
  let v:=a.hardware.inner.successor
  have ps:v.setup.SourcePitches ∧ 0<v.controlRegisters.dims.oldLanes ∧
      0<v.controlRegisters.dims.lanes ∧ 0<v.controlRegisters.dims.blocks:=by
    apply ResetOutput.sheet_pitches
    · exact g.argPositive
    · exact Nat.two_pow_pos _
  have main:=Nat.mul_le_mul_right a.w (a.inputs.sheets_bill ps.1 ps.2.1 ps.2.2.1 ps.2.2.2)
  rw [a.inputs.sheet_parts,Finset.sum_mul] at main
  exact main

end
end Hierarchy.DescentSixParty.RegisteredReset.Sample

end OAI
