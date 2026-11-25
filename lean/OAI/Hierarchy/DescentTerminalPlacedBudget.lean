import OAI.Hierarchy.DescentTerminalPlacedTariff
import OAI.Hierarchy.DescentTerminalChipBootExtent
import OAI.Hierarchy.DescentTerminalBankCalibration

namespace OAI
/-! # A single integral invoice at the selected stage's original exterior scale -/
namespace Hierarchy.DescentCompiler.TerminalScale
open DescentTerminalCompiledPrefix.AddressPlan

/-- Charge the complete placed terminal CPU, its seven-column instruction image,
the original four proposed-word views, and all six fixed chip ROMs.
The mask/scalar bill, common-position sweep and largest real row purchase have
their respective established integral prices at the exact same word width. -/
theorem joined_terminal_bill {T M copies s E h word factor rate wRows K W home blocks sockets tables privateCost time : ℕ}
    (cpu:word≤factor*h) (origin:copies=2^(K+(K+W))) (pack:h≤32*(2^K*s))
    (full:sockets=E*2^(K+W))
    (mask:privateCost*word*T≤22491*factor*(M*(copies*s)))
    (sweep:(4+(home+1)*(26+234*blocks))*h*T≤M*(copies*s))
    (rows:wRows*word*T≤rate*((copies*s)*(M+T*E)))
    (rom:(2^(h/2))*h*T≤M*(copies*s)) (buy:tables≤86*(2^(h/2))+344*wRows+43)
    (measured:time≤privateCost+115*(tables+1)+24*(4+(home+1)*(26+234*blocks))+
      131072*(home+sockets+wRows+1)) :
    (time+(8*wRows+12*2^(h/2)+20))*word*T≤
      (22491*factor+115*(130*factor+344*rate)+24*factor+131072*(factor+32*factor+rate)+8*rate+32*factor)*
        ((copies*s)*(M+T*E)) := by
  let money:=(copies*s)*(M+T*E)
  let fund:=M*(copies*s)
  let sweep_:=(4+(home+1)*(26+234*blocks))
  let R:=2^(h/2)
  have toMoney:fund≤ money:=by dsimp [fund,money];rw [Nat.mul_add,Nat.mul_comm M (copies*s)];omega
  have scaled (v:ℕ) (a:v*h*T≤fund) : v*word*T≤factor*money:=by
    calc
      _ ≤ v*(factor*h)*T := Nat.mul_le_mul_right T (Nat.mul_le_mul_left v cpu)
      _ = factor*(v*h*T) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (a.trans toMoney)
  have single:1≤R:=Nat.two_pow_pos _
  have rPrice:=scaled R rom
  have one:word*T≤factor*money:=by
    calc
      _ ≤ R*word*T := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ single)
      _ ≤ _ := rPrice
  have hs:home+1≤ sweep_:=by
    have v:=Nat.le_mul_of_pos_right (home+1) (show 0<26+234*blocks by omega);dsimp [sweep_];omega
  have sPrice:=scaled sweep_ sweep
  have homePrice:=Nat.mul_le_mul_right T (Nat.mul_le_mul_right word hs)
  have socketsPrice: sockets*word*T≤32*factor*money:=by
    have x:=packet_bill copies s E K W h word factor origin pack cpu
    have y:((copies*s)*E)*T≤ money:=by dsimp [money];rw [Nat.mul_add];nlinarith only [Nat.zero_le (copies*s*M)]
    calc
      _ ≤ ((32*factor)*(copies*s)*E)*T := by rw [full];exact Nat.mul_le_mul_right _ x
      _ = (32*factor)*(((copies*s)*E)*T) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ y
  have tablePrice:=Nat.mul_le_mul_right T (Nat.mul_le_mul_right word buy)
  have charge:=Nat.mul_le_mul_right T (Nat.mul_le_mul_right word measured)
  have privatePrice:=mask.trans (Nat.mul_le_mul_left (22491*factor) toMoney)
  change _≤_*money
  change wRows*word*T≤rate*money at rows
  change tables*word*T≤(86*R+344*wRows+43)*word*T at tablePrice
  dsimp only [sweep_,R] at *
  simp only [Nat.add_mul,Nat.mul_assoc] at charge tablePrice homePrice privatePrice rPrice sPrice socketsPrice rows one ⊢
  omega

end Hierarchy.DescentCompiler.TerminalScale

end OAI
