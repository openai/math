import OAI.Hierarchy.DescentPacketFactorShape
import OAI.Hierarchy.DescentFallbackPacket
import OAI.Hierarchy.DescentRotorWindowSize
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # Scale of the fallback and matrix packet field counts -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale
noncomputable section

private def fallbackCoefficient (D n : ℕ) := 1+D+2+(D+1)*(2^n+1)^2
private def matrixCoefficient (D : ℕ) := 1+D+2+(1+D*(D*6))
private def packetCoefficient (D n : ℕ) := fallbackCoefficient D n+matrixCoefficient D+1
def packetRateLead (D n : ℕ) := 300000*packetCoefficient D n

/-- A single active field or a block contributes linearly to the native invoice. -/
private theorem factor_le {fields blocks limit : ℕ} (pos : 0<limit) (hf : fields≤limit) (hb : blocks≤limit) :
    DescentPacketPullInvoiceVolume.factor fields blocks ≤ 50000*limit := by
  simp only [DescentPacketPullInvoiceVolume.factor,DescentPlacedInvoiceVolume.volumeFactor,Nat.one_mul,Nat.mul_one]
  omega

theorem packet_factor_le (D n rate j k cap growth : ℕ) (window : 2^k≤ scale j rate)
    (capacity : cap≤ scale j rate) (stage : growth≤ scale j rate) :
    (DescentPacketPullInvoiceVolume.factor (DescentFallbackPeriod.inputCount D (2^k) cap n k) (2^k)+
      DescentPacketPullInvoiceVolume.factor (DescentRotorWindowArchive.count D (2^k) cap) (2^k))*(growth+2) ≤
        packetRateLead D n*scale j (5*rate) := by
  let z:=scale j rate
  let Y:=2^n+1
  let b:=z^4
  have positive : 0<z:=Nat.two_pow_pos _
  have z₄ : z≤b:=by simpa only [pow_one] using (Nat.pow_le_pow_right positive (by decide : 1≤4))
  have z₂ : z^2≤b:=Nat.pow_le_pow_right positive (by decide : 2≤4)
  have small : 2^k≤b:=window.trans z₄
  have logical : (2^k)*(2*cap)≤2*b := calc
    _ ≤ z*(2*z) := Nat.mul_le_mul window (Nat.mul_le_mul_left _ capacity)
    _ = 2*z^2 := by ring
    _ ≤ 2*b := Nat.mul_le_mul_left _ z₂
  have square : (2^k)*(2^k)≤b:=by
    apply le_trans (Nat.mul_le_mul window window)
    simpa only [pow_two] using z₂
  have padded : DescentFallbackShapeTable.rows k (2^n) ≤ z^2*Y := by
    change ((k+1)*2^k)*Y ≤ z^2*Y
    apply Nat.mul_le_mul_right Y
    simpa only [pow_two] using Nat.mul_le_mul ((Nat.lt_two_pow_self (n:=k)).trans_le window : k+1≤z) window
  have diary : DescentSharedBookScan.width k (2^n) D ≤ (D+1)*Y^2*b := calc
    _ ≤ (z^2*Y)*((D+1)*(z^2*Y)) := Nat.mul_le_mul padded (Nat.mul_le_mul_left _ padded)
    _ = (D+1)*Y^2*b := by dsimp [b]; ring
  have fb : DescentFallbackPeriod.inputCount D (2^k) cap n k ≤ fallbackCoefficient D n*b := calc
    _ ≤ b+D*b+(2*b+(D+1)*Y^2*b) :=
      Nat.add_le_add (Nat.add_le_add small (Nat.mul_le_mul_left _ small)) (Nat.add_le_add logical diary)
    _ = _ := by dsimp [fallbackCoefficient,Y]; ring
  have basepos : 0<b:=pow_pos positive _
  have mx : DescentRotorWindowArchive.count D (2^k) cap ≤ matrixCoefficient D*b := calc
    _ ≤ b+D*b+2*b+(b+D*(D*6)*b) :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add small (Nat.mul_le_mul_left _ small)) logical)
        (Nat.add_le_add square (Nat.le_mul_of_pos_right _ basepos))
    _ = _ := by dsimp [matrixCoefficient]; ring
  let C:=packetCoefficient D n
  have cpos : 0<C:=Nat.succ_pos _
  have hfb : fallbackCoefficient D n≤C:=by dsimp [C,packetCoefficient]; omega
  have hmx : matrixCoefficient D≤C:=by dsimp [C,packetCoefficient]; omega
  have block : 2^k ≤ C*b:=small.trans (Nat.le_mul_of_pos_left _ cpos)
  have room : 0<C*b:=Nat.mul_pos cpos basepos
  have first:=factor_le room (fb.trans (Nat.mul_le_mul_right _ hfb)) block
  have next:=factor_le room (mx.trans (Nat.mul_le_mul_right _ hmx)) block
  have grow : growth+2≤3*z:=by change growth≤z at stage; omega
  have pow5 : z^5=scale j (5*rate):=by
    dsimp [z,scale]
    rw [←Nat.pow_mul]
    congr 1; ring
  calc
    _ ≤ (50000*(C*b)+50000*(C*b))*(3*z) := Nat.mul_le_mul (Nat.add_le_add first next) grow
    _ = packetRateLead D n*z^5 := by dsimp only [C,b,packetRateLead]; ring
    _ = _ := by rw [pow5]

theorem packet_factor_rate (D n rate : ℕ) :
    ∃lead exp : ℕ,∀j k cap growth,2^k≤ scale j rate → cap≤ scale j rate → growth≤ scale j rate →
      (DescentPacketPullInvoiceVolume.factor (DescentFallbackPeriod.inputCount D (2^k) cap n k) (2^k)+
       DescentPacketPullInvoiceVolume.factor (DescentRotorWindowArchive.count D (2^k) cap) (2^k))*(growth+2) ≤
       lead*scale j exp :=
  ⟨packetRateLead D n,5*rate,packet_factor_le D n rate⟩

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
