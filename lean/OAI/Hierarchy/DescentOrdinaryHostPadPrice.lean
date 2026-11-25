import OAI.Hierarchy.DescentOrdinaryHostPad
import OAI.Hierarchy.DescentPackedColumnHardware
import OAI.Hierarchy.DescentTerminalPrimitiveSpace

namespace OAI
/-! Instruction names, RAM ticks and the extent of a zero-padded or truncated host rectangle. -/
namespace Hierarchy.DescentOrdinaryHostPad.Rect
open DescentSIMDLookup DescentStaticWordColumn ProtocolRAM
noncomputable section
variable (R : Rect) (base : ℕ) (src : Fin R.pages→Bank) (w : ℕ)

theorem fee : (R.phase base src w).ticks+7*names (R.phase base src w).program ≤ 512*(R.pages+1)*(R.rows+1) :=by
  have work (i : ℕ) (hi : i < R.pages) : (R.column src i).work ≤ 7 :=by
    simpa only [column,dite_eq_left hi] using (show (Expr.lookup (src ⟨i,hi⟩) .row).work ≤ 7 from le_rfl)
  have time_:=DescentPackedFlowBatch.tariff (base) R.kept R.rows R.pages (R.column src) 7 work
  have labels:=DescentOperandVectorArena.names_passes (base) R.kept R.rows w 7 (R.column src) 0
    R.pages (fun i hi small=>work i (by simpa using small))
  have inside : R.kept ≤ R.rows:=Nat.min_le_right ..
  have common:=Nat.mul_le_mul_left R.pages inside
  change (4+((R.pages+1)*R.rows)*6+clock (R.copies base src))+
    7*names ((scan w (base) ((R.pages+1)*R.rows) (.lit 0)).seq
      (program w (R.copies base src))) ≤ _
  rw [names_seq,names_scan]
  change clock (R.copies base src) ≤ 4+R.pages*(4+R.kept*(2*7+4)) at time_
  change names (program w (R.copies base src)) ≤ 15+R.pages*(11+4*7) at labels
  change (4+((R.pages+1)*R.rows)*6+clock (R.copies base src))+
    7*(15+names (program w (R.copies base src))) ≤ _
  nlinarith only [time_,labels,common,Nat.zero_le R.pages,Nat.zero_le R.rows,Nat.zero_le (R.pages*R.rows)]

theorem cofinal_fee (factor h : ℕ) (bus : w+1 ≤ factor*h) :
    ((R.phase base src w).ticks+7*names (R.phase base src w).program)*(w+1) ≤
    (512*(R.pages+1)*(R.newH*chunks R.groups R.lanes+1))*(factor*h) :=
  Nat.mul_le_mul (R.fee base src w) bus

theorem extent : R.finish base ≤ base+(R.pages+3)*(R.rows+1)+1 :=by
  have round : 2^Nat.clog 2 (R.rows+1) ≤ 2*(R.rows+1)+1 :=DescentTerminalPrimitiveArena.pad_le _
  change base+(R.pages+1)*R.rows+2^Nat.clog 2 (R.rows+1) ≤ _
  nlinarith only [round,Nat.zero_le R.pages]

end
end Hierarchy.DescentOrdinaryHostPad.Rect

end OAI
