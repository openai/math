import OAI.Hierarchy.DescentOrdinaryBornBudget
import OAI.Hierarchy.DescentOrdinaryBornBook
import OAI.Hierarchy.DescentPackedColumnHardware

namespace OAI
/-! # Cost of publishing newborn operands from the mounted donor chip -/
namespace Hierarchy.DescentOrdinaryBorn.Chart
open DescentPackedZip DescentSIMDLookup DescentStaticWordColumn ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (B : Chart)

theorem expr_price (old : Bank) (floor n : ℕ) (actual : n<B.fields) : (B.expr old floor n).work≤32:=by
  unfold expr
  rw [dite_eq_left actual]
  exact DescentOperandFamilyBook.expr_work B.law B.lanes floor _ (query old) 7 (fun _=>le_rfl)

theorem tariff (old : Bank) (floor w : ℕ) :
    B.ticks old floor≤B.cpu ∧ DescentStaticWordColumn.names (B.program old floor w)≤B.textCost:=by
  constructor
  · exact Nat.add_le_add le_rfl (DescentPackedFlowBatch.tariff (B.output floor) B.rows B.pitch B.fields
      (B.expr old floor) 32 (B.expr_price old floor))
  · have book : DescentStaticWordColumn.names (DescentOperandFamilyBook.program B.law B.lanes floor w)=15*(B.bookWords+1):=by
      unfold DescentOperandFamilyBook.program Book.install
      rw [names_mount]
      rfl
    rw [program,names_seq,book]
    exact Nat.add_le_add le_rfl (DescentOperandVectorArena.names_passes (B.output floor) B.rows B.pitch w 32
      (B.expr old floor) 0 B.fields (fun i _ h=>B.expr_price old floor i (by omega)))

end
end Hierarchy.DescentOrdinaryBorn.Chart

end OAI
