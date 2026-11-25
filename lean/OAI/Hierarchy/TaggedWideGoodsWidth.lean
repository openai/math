import OAI.Hierarchy.ProtocolRAMCalendarHeld
import OAI.Hierarchy.ProtocolRAMCalendarMesh
import OAI.Hierarchy.ProtocolRAMFeed

namespace OAI
/-! # The native width of the actual commodity bond at a calendar date -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing
noncomputable section

/-- Read consumed slices in their original order. Their number is a fixed
calendar parameter, so this expression has height-independent control size. -/
def heldExpr (bank : Bank) (stride steps : ℕ) (saved : Expr) : ℕ → Expr
  | 0=>saved
  | j+1=>if j<steps then .op .sub (heldExpr bank stride steps saved j)
              (.lookup bank (.op .add (.lit (j*stride)) saved))
           else heldExpr bank stride steps saved j

theorem heldExpr_read {W : ℕ} (bank : Bank) (stride steps : ℕ) (saved : Expr) (j : ℕ)
    (m : Memory W) (r : Word W) (v : ℕ) (read : saved.eval m r=(v:Word W))
    (sliceRead : ∀i<steps,bank.read m ((i*stride+v:ℕ):Word W)=(slice steps v i:Word W)) :
    (heldExpr bank stride steps saved j).eval m r=(held steps v j:Word W) := by
  induction j with
  | zero=>simpa [heldExpr,held_start] using read
  | succ i ih=>
    have bal := held_step steps v i
    by_cases active : i<steps
    · simp only [ite_eq_left active] at bal
      simp only [heldExpr,ite_eq_left active,Expr.eval,RowOp.opcode,BinaryOp.eval,ih,read]
      rw [←Nat.cast_add,sliceRead i active,bal,Nat.cast_add,add_sub_cancel_right]
    · simp only [ite_eq_right active,Nat.add_zero] at bal
      simpa only [heldExpr,ite_eq_right active,←bal] using ih

/-- Parcel already in the commodity bank, the remaining public payload
at its original payload wire, and the actually bought but unspent reserve. -/
def goodsWidth (bank : Bank) (stride : ℕ) (mesh : Mesh) (payload p j : ℕ)
    (active saved payloadRow parentMode : Expr) : Expr :=
  .op .add (.op .add active (.branch .eq payloadRow (.lit 0) (.lit 0) (.lit (held mesh.inject payload p))))
    (.branch .eq parentMode (.lit 3) (heldExpr bank stride mesh.reserveSteps saved j) (.lit 0))

theorem goodsWidth_read {W : ℕ} (bank : Bank) (stride : ℕ) (mesh : Mesh) (payload p j : ℕ)
    (active saved payloadRow parentMode : Expr) (m : Memory W) (row : Word W) (a v : ℕ)
    (hasPayload bought : Bool) (readActive : active.eval m row=(a:Word W))
    (readSaved : saved.eval m row=(v:Word W))
    (payloadCode : payloadRow.eval m row=0 ↔ hasPayload=false)
    (parentCode : parentMode.eval m row=(3:Word W) ↔ bought=true)
    (sliceRead : ∀i< mesh.reserveSteps,bank.read m ((i*stride+v:ℕ):Word W)=
        (slice mesh.reserveSteps v i:Word W)) :
    (goodsWidth bank stride mesh payload p j active saved payloadRow parentMode).eval m row=
      ((a+held mesh.inject payload p*hasPayload.toNat+(if bought then held mesh.reserveSteps v j else 0):ℕ):Word W) := by
  have rest := heldExpr_read bank stride mesh.reserveSteps saved j m row v readSaved sliceRead
  cases hasPayload <;> cases bought <;>
    simp_all [goodsWidth,Expr.eval,Comparison.test,RowOp.opcode,BinaryOp.eval,Nat.cast_add]

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
