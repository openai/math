import OAI.Hierarchy.DescentDatedResetOutput
import OAI.Hierarchy.DescentResetOperandSetup

namespace OAI
/-! Conversion from the common decoder width to the successor's stored operand width. -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentResetOperandSetup DescentSIMDLookup DescentPackedZip ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
variable (v : ResetOutput)

def keepWidth (_ : Fin 1) :=v.setup.fieldBits
def keptValue (base : ℕ) (raw : Expr) : Expr :=
  DescentOperandInputCast.expr v.keepWidth v.receiver.valueBits v.setup.fieldBits v.receiver.lanes (v.keepBase base) 0 raw
def keepBook (base w : ℕ) : Code w :=
  ⟨DescentOperandInputCast.program v.keepWidth v.receiver.valueBits v.setup.fieldBits v.receiver.lanes (v.keepBase base) w,
    4+10*v.keepWords,
    DescentOperandInputCast.image v.keepWidth v.receiver.valueBits v.setup.fieldBits v.receiver.lanes (v.keepBase base)⟩

theorem keep_end (base : ℕ) : DescentOperandInputCast.endAddress (v.keepBase base) 1 v.setup.fieldBits v.receiver.lanes=
    v.operandStart base:=by simp [operandStart,keepWords,DescentOperandInputCast.endAddress,DescentOperandInputCast.words]

theorem keep_before (base : ℕ) : v.keepBase base≤v.operandStart base:=by
  rw [←v.keep_end]
  exact Nat.le_add_right ..

theorem keep_any {w : ℕ} (base : ℕ) (m : Memory w) (room : v.operandStart base<2^w) :
    Code.Runs (v.keepBook base w) (v.keepBase base) (v.operandStart base) m:=by
  have actual:=DescentOperandInputCast.any v.keepWidth v.receiver.valueBits v.setup.fieldBits v.receiver.lanes
    (v.keepBase base) m (fun _=>le_rfl) ((v.keep_end base).le.trans_lt room)
  refine ⟨actual.1,actual.2.1,?_⟩
  intro z outside
  apply actual.2.2.1 z
  simpa only [v.keep_end] using outside

theorem keptValue_fits {w : ℕ} (base : ℕ) (raw : Expr) (fit : raw.Fits w (v.keepBase base))
    (room : v.operandStart base<2^w) : (v.keptValue base raw).Fits w (v.operandStart base):=by
  rw [←v.keep_end base] at room ⊢
  exact DescentOperandInputCast.expr_fits v.keepWidth v.receiver.valueBits v.setup.fieldBits v.receiver.lanes
    (v.keepBase base) 0 raw le_rfl fit room

theorem keptValue_source {w H G : ℕ} (base : ℕ) (raw : Expr) (m : Memory w)
    (values : Fin H→Fin G→Cell v.setup.fieldBits) (fit : raw.Fits w (v.keepBase base))
    (read : Source raw values v.receiver.lanes m) (room : v.operandStart base<2^w) :
    Source (v.keptValue base raw) (fun h g=>(values h g).val : Fin H→Fin G→Cell v.receiver.valueBits)
      v.receiver.lanes ((v.keepBook base w).image m) :=
  (DescentOperandInputCast.issued v.keepWidth v.receiver.valueBits v.setup.fieldBits v.receiver.lanes
    (v.keepBase base) 0 raw m values (fun _=>le_rfl) fit read ((v.keep_end base).le.trans_lt room)).2

theorem keptValue_work (base : ℕ) (raw : Expr) : (v.keptValue base raw).work=raw.work+12:=by
  unfold keptValue DescentOperandInputCast.expr
  rw [DescentPackedZip.work]
  simp [Expr.work,Nat.add_assoc]

theorem keep_names (base w : ℕ) : DescentStaticWordColumn.names (v.keepBook base w).program=15*(v.keepWords+1):=by
  change DescentStaticWordColumn.names (DescentStaticWordColumn.program w (v.keepBase base) _ v.keepWords)=_
  exact DescentStaticWordColumn.names_mount ..

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
