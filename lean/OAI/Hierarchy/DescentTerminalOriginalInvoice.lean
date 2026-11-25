import OAI.Hierarchy.DescentTerminalEndgameInvoice
import OAI.Hierarchy.DescentTerminalPublicIdentity

namespace OAI
/-! # Actual terminal RAM and all sixteen original input columns -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentStaticWordColumn DescentTerminalVertexFields DescentCompiler.TerminalScale DescentSixParty
open DescentTerminalGraphVolume DescentTerminalDenseWindow DescentTerminalBinReaddress
noncomputable section
variable {blocks v B:ℕ} (V:Home.Format) (I:Input) (R:MaskAllocation.Channels blocks)
variable (start header:ℕ) (short:v*span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤B)
variable (literal:DescentTerminalEmitter.Compact.Literals I.sources)
variable (T M copies s E rate piece q W homes j r lanes h bw factor:ℕ) (positive:0<homes) (wPos:0<W)
local notation "p" => W*piece
local notation "d" => copies*s
local notation "total_" => integralFrontier T M d E rate
local notation "budget" => rowBudget p q W total_ (d*E) homes 3
local notation "n" => bought budget W
local notation "K" => binCount budget W
local notation "S" => dimensions homes positive budget W total_ (q*p) E j r lanes
local notation "C" => meter V R start
local notation "O" => registers V S R start header
local notation "ba" => afterMeter V S R start
local notation "cpu" => clock V S I R start header short literal (bw:=bw)
local notation "ticks" => time V S I R start header
local notation "cap_" => cohortSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
 (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=blocks)
local notation "sz" => channelSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
 (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=blocks)
local notation "cells" => MaskAllocation.marks sz+cap_
local notation "masked" => privateMaskedClock cells cap_ homes blocks V.piece+7*privateMaskedNames cells cap_ blocks V.piece
local notation "fund" => d*(M+T*E)
local notation "ρ" => 2*(6*(32*factor)*(3+4*rate)+2*factor)

include wPos in
theorem endgame_original_price (codes:ℕ) (src:DescentTerminalChipRuntime.Banks)
    (spanFit:W≤2^(h/2)) (large:10≤h) (support:2^h≤2*(M*copies)) (width:T≤ s)
    (arch:bw≤factor*h) (packed:h≤32*(q*p))
    (outside:copies=2^(j+(j+r))) (pack0:h≤32*((2^j)*s))
    (positions:(4+(homes+1)*(26+234*blocks))*h*T≤M*d)
    (privateBill:masked*bw*T≤22491*factor*(M*d))
    (idx:I.indexEvents≤2*n) (fmt:I.formatEvents≤2*n)
    (tables:∀f,DescentTerminalEmitter.Compact.need (I.sources f)≤2^(h/2)+4*n)
    (dense:formatBits q p+2*(q*p)≤h/2) (route:DescentTerminalBinFormat.controlBits W q+sliceWidth W q piece≤h/2)
    (alphabet:codes+1≤2^(h/2)) :
    (ticks+DescentTerminalChipRuntime.clocks n n+
       7*(names cpu+names (DescentTerminalChipRuntime.program (chip S I ba) src bw n n))+
       DescentTerminalPublicIdentity.total K W q piece codes (S).terminal.plane.rawRows (S).terminal.plane.publicRows)*bw*T≤
      (22491*factor+115*(130*factor+344*ρ)+24*factor+131072*(factor+32*factor+ρ)+11*ρ+101*factor)*fund := by
  let raw:=(S).terminal.plane.rawRows
  let num:=(S).terminal.plane.publicRows
  let privateCells:=DescentTerminalPrimitiveArena.pad raw
  have rawPay:=endgame_payload_price V I R start header short literal T M copies s E rate piece q W homes j r lanes h bw factor
    positive wPos codes privateCells src spanFit large support width arch packed outside pack0 positions privateBill idx fmt tables
    dense route alphabet (DescentTerminalPrimitiveArena.pad_le raw)
  have sockets:=packet_bill copies s E j r h bw factor outside pack0 arch
  have packet: num*bw*T≤32*factor*fund:=calc
    _ ≤ ((32*factor)*(copies*s)*E)*T := Nat.mul_le_mul_right _ sockets
    _ = (32*factor)*(d*(T*E)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_add_left _ _))
  have single:bw*T≤factor*fund:=calc
    _ ≤ (factor*h)*T := Nat.mul_le_mul_right _ arch
    _ = factor*(h*T) := by ring
    _ ≤ factor*((M*copies)*s) := Nat.mul_le_mul_left _ (Nat.mul_le_mul
      ((Nat.le_mul_of_pos_left h (Nat.two_pow_pos _)).trans (table_fund large support)) width)
    _ = factor*(d*M) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
  have plus: DescentTerminalPrimitiveArena.pad num*bw*T≤65*factor*fund:=calc
    _ ≤ (2*num+1)*bw*T := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (DescentTerminalPrimitiveArena.pad_le num))
    _ = 2*(num*bw*T)+(bw*T) := by ring
    _ ≤ 2*(32*factor*fund)+factor*fund := Nat.add_le_add (Nat.mul_le_mul_left _ packet) single
    _ = _ := by ring
  change (_+(DescentTerminalBoot.total K W q piece codes+privateCells+
    DescentTerminalPrimitiveArena.pad num))*bw*T≤_
  let cycles:=ticks+DescentTerminalChipRuntime.clocks n n+
    7*(names cpu+names (DescentTerminalChipRuntime.program (chip S I ba) src bw n n))
  change (cycles+(DescentTerminalBoot.total K W q piece codes+privateCells+
      DescentTerminalPrimitiveArena.pad num))*bw*T≤_
  rw [show (cycles+(DescentTerminalBoot.total K W q piece codes+privateCells+
    DescentTerminalPrimitiveArena.pad num))*bw*T=
    (cycles+DescentTerminalBoot.total K W q piece codes+privateCells)*bw*T+
      DescentTerminalPrimitiveArena.pad num*bw*T by ring]
  exact (Nat.add_le_add rawPay plus).trans_eq (by ring)
end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
