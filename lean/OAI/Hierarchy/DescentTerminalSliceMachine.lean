import OAI.Hierarchy.DescentTerminalSliceExecution
import OAI.Hierarchy.DescentTerminalSlicePanel
import OAI.Hierarchy.DescentTerminalPointerPairPrice

namespace OAI
/-! # Original physical gather, six shared ROMs and authentic word readback -/
namespace Hierarchy.DescentTerminalSliceShelf
open DescentTerminalPointerDigits DescentOperandStateBanks DescentSIMDLookup ProtocolRAM DescentStaticWordColumn
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {L d H blocks w:ℕ} {width:Fin 6→ℕ}
variable (base:ℕ) (chart:Fin L→Fin blocks→Gather.Address)
    (write:(f:Fin 6)→(Fin L→Cell d)→Cell (width f))
local notation "rows" => blocks*H
local notation "sweep" => Gather.dropOff base blocks H L chart
variable (m:Memory w) (ok:∀j x,(chart j x).Fits base H w) (off:2^d<2^w) (room:fence base L d (blocks*H)<2^w)
theorem names_prefix (r w base n:ℕ) (le_:n≤6) :
    names («prefix» write r w base n le_) =
      15+n*(15*(DescentTerminalPointerFrame.size L d+1)+(35+52*L)) := by
  induction n with
  | zero=>simp only [«prefix»,ProtocolRAM.program,names_scan,Nat.zero_mul,Nat.add_zero];rfl
  | succ n ih=>
    rw [«prefix»,names_seq,ih,DescentTerminalPointerDigits.shared_hardware]
    ring

include m ok off room in
omit off in
theorem invoice {h factor:ℕ} (positive:0<H)
    (static:DescentTerminalPointerFrame.size L d≤2*2^(h/2))
    (work:(L+1)*(blocks+1)≤factor) :
    names (program base chart write H w)+cost base chart H d≤
      16384*(2^(h/2)+H*factor) := by
  have bound:=Gather.fetch_names w base H L blocks chart 0 (L*blocks)
  have calcRun:=Gather.fetch_blocks chart m base H ok
    (show base+(L*blocks)*H<2^w by
      have e:=monotone base L d rows (Nat.zero_le 6)
      rw [Nat.mul_assoc]
      apply Nat.lt_of_le_of_lt _ (e.trans_lt room)
      simp [stage,Gather.rom,DescentOperandStateBanks.guard])
  have time:=calcRun.2.2.2.2
  have one:0<2^(h/2):=Nat.two_pow_pos _
  have mul:=Nat.mul_le_mul_left H work
  unfold program cost
  rw [names_seq,names_prefix]
  change names (ProtocolRAM.program w sweep)+_+(_+clocks L d rows 6)≤_
  unfold clocks
  change names (ProtocolRAM.program w sweep)≤_ at bound
  change clock sweep≤_ at time
  nlinarith only [bound,time,static,work,mul,one,positive,Nat.zero_le (L*H),
    Nat.zero_le (blocks*H),Nat.zero_le (blocks*L*H),Nat.zero_le (H*factor),Nat.zero_le (L*blocks),
    Nat.mul_le_mul_right (L*blocks) (Nat.succ_le_of_lt positive)]

end
end Hierarchy.DescentTerminalSliceShelf

end OAI
