import OAI.Hierarchy.DescentTerminalPreflightChipInput
import OAI.Hierarchy.DescentTerminalRouteEarlier

namespace OAI
/-! # Every earlier sparse-header, booked-route and scalar operand on the fixed chip -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalCompiledPrefix DescentTerminalRowArena
open DescentTerminalEmitter.Compact DescentTerminalPaidHeaderEvents DescentTerminalHeaderDraft
open DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (x : Spec) (begin_ rom q grain : ℕ) (peer : Bank) (old : Fin x.scalar.blocks→Fin (2*x.cap)→Bank)
    (total modulo homes : Bank) (boundary : ℕ)
local notation "A_" => x.draft begin_ total modulo homes boundary
local notation "lit" => literals (x.literalBase begin_) x.paidRows
local notation "tab" => DescentTerminalHeaderDraft.output A_
variable (cfg : DescentTerminalCompiledPrefix.Shape) (other : AddressPlan.Input)
local notation "I_" => chipInput x begin_ rom q grain peer old total modulo homes boundary cfg other

private theorem operand_cases (P : Bank → Prop) (src : Fixed) (out : Output) (j : ℕ)
    (half : P src.half) (lane : P src.lane) (identity : P src.identity) (zero : P src.zero)
    (active : P out.active) (mode : P out.mode) (source : P out.source) : P (operand src out j) := by
  unfold operand
  split <;> assumption

/-- Attained words of the first 24 operands all lie in the original four static
bands or in one of the three mutable row-publication bands. -/
theorem chip_earlier {ceiling : ℕ} (room : x.maskBase begin_≤ceiling) :
    DescentTerminalEmitter.Compact.Earlier ceiling (I_).sources := by
  obtain ⟨_,_,_,_,_,_,_,_,tail⟩:=x.layers begin_
  have literal (j : ℕ) (hj : j<4) :
      (literalBank (x.literalBase begin_) x.paidRows j).base+
        (literalBank (x.literalBase begin_) x.paidRows j).size≤ceiling := by
    apply le_trans _ (tail.trans room)
    have mul := Nat.mul_le_mul_right (span x.paidRows) (show j+1≤4 by omega)
    rw [Nat.succ_mul] at mul
    change x.literalBase begin_+j*span x.paidRows+span x.paidRows≤x.literalBase begin_+4*span x.paidRows
    omega
  have top : stop A_≤ceiling := (x.draft_end begin_ total modulo homes boundary).le.trans room
  have issued (j : ℕ) (hj : j<3) : (newBank A_ j).base+(newBank A_ j).size≤ceiling := by
    apply le_trans _ top
    have mul := Nat.mul_le_mul_right (2^Nat.clog 2 (A_).rows) (show j+1≤3 by omega)
    rw [Nat.succ_mul] at mul
    change (A_).finish+j*(2^Nat.clog 2 (A_).rows)+(2^Nat.clog 2 (A_).rows)≤(A_).finish+3*(2^Nat.clog 2 (A_).rows)
    omega
  have saved (j : ℕ) : (operand lit tab j).base+(operand lit tab j).size≤ceiling :=
    operand_cases (fun bank => bank.base + bank.size ≤ ceiling) lit tab j
      (literal 0 (by decide)) (literal 1 (by decide)) (literal 2 (by decide)) (literal 3 (by decide))
      (issued 0 (by decide)) (issued 1 (by decide)) (issued 2 (by decide))
  intro j b paid
  change columns lit tab (fun _=>.attained (lit).zero) j=.attained b at paid
  by_cases small : j.val<24
  · have same : operand lit tab j.val=b := by simpa [columns,small] using paid
    exact same ▸ saved j.val
  · have same : (lit).zero=b := by simpa [columns,small] using paid
    exact same ▸ literal 3 (by decide)

variable (T : AddressPlan.RouteSources.Tables) (base t H N A p vertices W B pool : ℕ)
local notation "row_" => AddressPlan.rowArena cfg I_ base
local notation "routed_" => T.columns row_ (I_).sources
local notation "terminal_" => ScalarLiterals.columns q t H N A p vertices W B pool routed_

theorem priced_earlier (beginRoom : x.maskBase begin_≤base) :
    DescentTerminalEmitter.Compact.Earlier (AddressPlan.pageEnd cfg I_ base) terminal_ := by
  have below := (AddressPlan.stages cfg I_ base).1
  have root : base≤(row_).finish := (row_).start_le 22
  have prior := chip_earlier x begin_ rom q grain peer old total modulo homes boundary cfg other
    (beginRoom.trans (root.trans below))
  exact AddressPlan.RouteSources.scalar_earlier _ _ _ _ _ _ _ _ _ _ _
    (AddressPlan.RouteSources.earlier T row_ _ prior below)

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
