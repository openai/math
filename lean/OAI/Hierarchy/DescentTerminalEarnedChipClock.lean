import OAI.Hierarchy.DescentTerminalEndgameInvoice
import OAI.Hierarchy.DescentTerminalEarnedRates

namespace OAI
/-! # Terminal CPU and its chip on the actual issued shell and opcode width -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentStaticWordColumn DescentTerminalVertexFields DescentTerminalRowArena
open DescentCompiler.TerminalScale
noncomputable section
variable {blocks v B bw:ℕ} (V:Home.Format) (S:Shape) (I:Input) (R:MaskAllocation.Channels blocks)
variable (start header:ℕ) (short:v*span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤B)
variable (literal:DescentTerminalEmitter.Compact.Literals I.sources)
local notation "C" => meter V R start
local notation "O" => registers V S R start header
local notation "ba" => afterMeter V S R start
local notation "L" => layout S I ba O
local notation "cpu" => clock V S I R start header short literal (bw:=bw)
local notation "ticks" => time V S I R start header
local notation "cap_" => cohortSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
 (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=blocks)
local notation "sz" => channelSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
 (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=blocks)
local notation "cells" => MaskAllocation.marks sz+cap_
local notation "static" => DescentTerminalEmitter.Compact.wordsBought I.sources
local notation "oldLabels" => privateMaskedNames cells cap_ blocks V.piece
local notation "oldTicks" => privateMaskedClock cells cap_ S.sites blocks V.piece

open DescentTerminalGraphVolume DescentTerminalRowArena DescentTerminalCompiledPrefix
open DescentTerminalEmitter.Compact

/-- A nonempty bank rounds up to at most twice its occupied size. -/
private theorem arena_size_le_twice {n : ℕ} (positive : 0 < n) :
    DescentTerminalDataPlane.Arena.size n ≤ 2*n := by
  cases h : Nat.clog 2 (n+1) with
  | zero => simp [DescentTerminalDataPlane.Arena.size, h]; omega
  | succ k =>
    have prev := Nat.pow_lt_of_lt_clog (show k < Nat.clog 2 (n+1) by omega)
    simp only [DescentTerminalDataPlane.Arena.size, h, pow_succ]
    omega

theorem earned_row_capacity {h : ℕ} (set : EarnedCounts h S I)
    (occupied : S.terminal.plane.rawRows≤S.terminal.pool)
    (headers : S.terminal.plane.headerRows≤S.terminal.pool+1) :
    RowCap S L S.terminal.pool :=by
  have expand:=arena_size_le_twice (n:=S.terminal.plane.rawRows+2+(S.terminal.plane.publicRows+2)) (by omega)
  constructor
  · exact le_rfl
  · exact set.paid.le
  · exact set.leaves.le
  · change DescentTerminalDataPlane.Arena.size (S.terminal.plane.rawRows+2+(S.terminal.plane.publicRows+2))≤_
    have packets:=set.packets
    omega
  · have packets:=set.packets;omega
  · exact headers
  · exact set.paid.le
  · exact set.paid.le
  · change I.indexEvents≤2*S.terminal.pool
    rw [set.indices,set.paid];omega
  · change I.formatEvents≤2*S.terminal.pool
    rw [set.formats,set.paid];omega

/-- Both native programs retain their actual word size. The clock charge and all seven
opcode columns are priced at one plus that word size. -/
theorem earned_chip_clock {h T M copies width E j r factor rate : ℕ} (src : DescentTerminalChipRuntime.Banks)
    (set : EarnedCounts h S I) (occupied : S.terminal.plane.rawRows≤S.terminal.pool)
    (headers : S.terminal.plane.headerRows≤S.terminal.pool+1)
    (large : 10≤h) (support : 2^h≤2*(M*copies)) (spanFit : T≤width)
    (arch : bw+1≤factor*h) (origin : copies=2^(j+(j+r))) (pack : h≤32*((2^j)*width))
    (socket : S.packets=E*2^(j+r))
    (mask : (oldTicks+7*oldLabels)*(bw+1)*T≤22491*factor*(M*(copies*width)))
    (sweep : (4+(S.sites+1)*(26+234*blocks))*h*T≤M*(copies*width))
    (rows : S.terminal.pool*(bw+1)*T≤rate*((copies*width)*(M+T*E))) :
    (ticks+DescentTerminalChipRuntime.clocks S.terminal.rows S.terminal.pool+
      7*(names cpu+names (DescentTerminalChipRuntime.program (chip S I ba) src bw S.terminal.rows S.terminal.pool)))*
      (bw+1)*T≤(22491*factor+115*(130*factor+344*rate)+24*factor+
      131072*(factor+32*factor+rate)+8*rate+32*factor)*((copies*width)*(M+T*E)) :=by
  have cap:=earned_row_capacity V S I R start header set occupied headers
  have actual:=paid_program V S I R start header short literal S.terminal.pool cap src (bw:=bw)
  have digits:=capacity_with_rows I.sources set.literal
  have table : 2^(h/2)*h*T≤M*(copies*width):=calc
    _ ≤ (M*copies)*T := Nat.mul_le_mul_right _ (table_fund large support)
    _ ≤ (M*copies)*width := Nat.mul_le_mul_left _ spanFit
    _ = M*(copies*width) := by ring
  have charge:=joined_terminal_bill arch origin pack socket mask sweep rows table digits actual
  exact (Nat.mul_le_mul_right T (Nat.mul_le_mul_right (bw+1) (Nat.le_add_right _ _))).trans charge

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
