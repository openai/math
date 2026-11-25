import OAI.Hierarchy.DescentTerminalSliceMachine
import OAI.Hierarchy.DescentTerminalDatedSliceWidth
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Physical start, end, and tariff of the six normalized role banks -/
namespace Hierarchy.DescentTerminalSliceShelf
open DescentTerminalPointerDigits DescentCompiler.TerminalScale DescentOperandStateBanks ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

theorem source_before (base L d rows : ℕ) (f:Fin 6) :
    (field base L d rows f.val).base+(field base L d rows f.val).size≤fence base L d rows := by
  change stage base L d rows f.val+DescentTerminalPointerFrame.size L d+pad rows≤_
  have step:stage base L d rows f.val+DescentTerminalPointerFrame.size L d+pad rows=
      stage base L d rows (f.val+1):=by unfold stage;ring
  rw [step]
  exact monotone base L d rows f.isLt

theorem fence_le (base L d h shops blocks factor:ℕ)
    (table:DescentTerminalPointerFrame.size L d≤2*2^(h/2)) (localWork:(L+1)*(blocks+1)≤factor) :
    fence base L d (blocks*shops)≤base+128*(2^(h/2)+shops*factor) := by
  have guardRoom:pad (blocks*shops)≤2*(blocks*shops)+1:=DescentDyadicSpan.span_le _
  have dyad:0<2^(h/2):=Nat.two_pow_pos _
  have clock:=Nat.mul_le_mul_left shops localWork
  unfold fence stage Gather.rom DescentOperandStateBanks.guard
  change base+L*(blocks*shops)+pad (blocks*shops)+6*(DescentTerminalPointerFrame.size L d+pad (blocks*shops))≤_
  nlinarith only [guardRoom,table,clock,dyad,Nat.zero_le (L*blocks*shops),Nat.zero_le (blocks*shops),
    Nat.zero_le (L*shops),Nat.zero_le shops,Nat.zero_le (shops*factor)]

theorem factor_le (j κ α k A:ℕ) (resources:A≤ DescentCompiler.TerminalScale.scale j α) (pb:k≤κ*(j+1)) :
    (2+3*A+1)*(2^k+1)≤ DescentCompiler.TerminalScale.scale j (α+κ+4) := by
  have a : 1≤ DescentCompiler.TerminalScale.scale j α :=Nat.two_pow_pos _
  have b : 1≤ DescentCompiler.TerminalScale.scale j κ :=Nat.two_pow_pos _
  have bits:2^k≤ DescentCompiler.TerminalScale.scale j κ:=Nat.pow_le_pow_right (by decide) pb
  have a' : 2+3*A+1≤6*DescentCompiler.TerminalScale.scale j α:=by omega
  have b' : 2^k+1≤2*DescentCompiler.TerminalScale.scale j κ:=by omega
  have coeff:12≤ DescentCompiler.TerminalScale.scale j 4:=by
    apply Nat.le_trans (show 12≤2^4 by decide)
    apply Nat.pow_le_pow_right (by decide)
    omega
  have prod:=Nat.mul_le_mul a' b'
  have charge:=Nat.mul_le_mul_left (DescentCompiler.TerminalScale.scale j α*DescentCompiler.TerminalScale.scale j κ) coeff
  rw [←scale_mul,←scale_mul]
  nlinarith only [prod,charge]

end
end Hierarchy.DescentTerminalSliceShelf

end OAI
