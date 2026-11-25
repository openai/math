import OAI.Hierarchy.DescentPrivateGateScale

namespace OAI
/-! # Integer costs for the actual terminal row shelf and the final partial bin -/
namespace Hierarchy

namespace DescentTerminalGraphVolume

def rowBudget (p q W : ℕ) (total exterior positions degree : ℕ) :=
  2*(3*(2*total+exterior)/(q*p)+positions*(degree+3))+W
end DescentTerminalGraphVolume

namespace DescentSixParty
open DescentTerminalGraphVolume
/-- Integer part of the normalized total wire budget. Its rate depends only
on the chosen compiler, and its exterior term uses the original single-copy pin count. -/
def integralFrontier (T m copies pins rate : ℕ) := ((1+2*rate)*copies*(m+T*pins))/T


/-- The fee for the fixed bin bank and the one final partial physical bin.
Only the row and group overhead are charged per common position. -/
theorem paid_frontier (T m copies pins rate p q width homes degree word factor : ℕ)
    (packing : word≤factor*(q*p)) :
    rowBudget p q width (integralFrontier T m copies pins rate) (copies*pins) homes degree*word*T ≤
      (6*factor*(3+4*rate))*(copies*(m+T*pins))+
        (2*(homes*(degree+3))+width)*word*T := by
  let total:=integralFrontier T m copies pins rate
  let money:=copies*(m+T*pins)
  let exterior:=copies*pins
  let bought:=3*(2*total+exterior)/(q*p)
  have sockets : bought*(q*p)≤3*(2*total+exterior) := Nat.div_mul_le_self _ _
  have original : exterior*T≤ money := by
    dsimp [exterior,money]
    rw [Nat.mul_add]
    nlinarith only [Nat.zero_le (copies*m),show copies*pins*T=copies*(T*pins) by ring]
  have reserve : total*T≤(1+2*rate)*money := by
    simpa [total,money,integralFrontier,Nat.mul_assoc] using
      Nat.div_mul_le_self ((1+2*rate)*copies*(m+T*pins)) T
  have scan : bought*word*T≤factor*(3*(2*total+exterior))*T := calc
    _ ≤ bought*(factor*(q*p))*T := Nat.mul_le_mul_right T (Nat.mul_le_mul_left bought packing)
    _ = factor*(bought*(q*p))*T := by ring
    _ ≤ _ := Nat.mul_le_mul_right T (Nat.mul_le_mul_left factor sockets)
  have resource : (2*total+exterior)*T≤(3+4*rate)*money := by
    calc
      _ = 2*(total*T)+exterior*T := by ring
      _ ≤ 2*((1+2*rate)*money)+money := Nat.add_le_add (Nat.mul_le_mul_left 2 reserve) original
      _ = _ := by ring
  change (2*(bought+homes*(degree+3))+width)*word*T ≤ _*money+_
  calc
    _ = 2*(bought*word*T)+(2*(homes*(degree+3))+width)*word*T := by ring
    _ ≤ 2*(factor*(3*(2*total+exterior))*T)+(2*(homes*(degree+3))+width)*word*T :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 scan) _
    _ = (6*factor)*((2*total+exterior)*T)+(2*(homes*(degree+3))+width)*word*T := by ring
    _ ≤ (6*factor)*((3+4*rate)*money)+(2*(homes*(degree+3))+width)*word*T :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ resource) _
    _ = _ := by ring
end DescentSixParty

namespace DescentTerminalCompiledPrefix.AddressPlan

/-- All selected descriptions are embedded in one whole number of physical bins.
The final extra bin pays the end padding even when the quotient is exact. -/
def binCount (n W:ℕ) := n/W+1
def bought (n W:ℕ) := binCount n W*W

theorem cap_both {n W:ℕ} (positive:0<W) (wide:W≤n) :
    n≤bought n W ∧ bought n W≤2*n := by
  have smaller:=Nat.mod_lt n positive
  have split:=Nat.div_add_mod n W
  have previous:=Nat.div_mul_le_self n W
  unfold bought binCount
  rw [Nat.add_mul,one_mul]
  rw [Nat.mul_comm W (n/W)] at split
  omega
end DescentTerminalCompiledPrefix.AddressPlan

namespace DescentCompiler.TerminalScale
open DescentSixParty DescentTerminalGraphVolume
/-- A paid home scan covers the leftover group rows at the same positions.
One half-word fits the only residual bin; it is paid once for all positions
and epochs, in the same way as an installed shared ROM. -/
theorem covered_bank (T M populations s exterior rate p q W homes h word factor cpu blocks : ℕ)
    (room : W≤2^(h/2)) (large : 10≤h) (support : 2^h≤2*(M*populations))
    (power : T≤ s) (packed : word≤factor*(q*p)) (arch : word≤cpu*h)
    (positions : (4+(homes+1)*(26+234*blocks))*h*T≤M*(populations*s)) :
    let d:=populations*s
    (rowBudget p q W (integralFrontier T M d exterior rate) (d*exterior) homes 3)*word*T≤
      (6*factor*(3+4*rate)+2*cpu)*(d*(M+T*exterior)) := by
  let d:=populations*s
  let money:=d*(M+T*exterior)
  have total : M*d≤ money := by dsimp [money];rw [Nat.mul_add];nlinarith only [Nat.zero_le (d*(T*exterior))]
  have a : 12*homes*h*T≤M*d := by
    have bound : 12*homes≤4+(homes+1)*(26+234*blocks) := by
      have half:=Nat.mul_le_mul_left (homes+1) (show 12≤26+234*blocks by omega)
      omega
    exact (Nat.mul_le_mul_right T (Nat.mul_le_mul_right h bound)).trans positions
  have b : W*h*T≤M*d := calc
    _ ≤ (M*populations)*T := Nat.mul_le_mul_right T
      ((Nat.mul_le_mul_right h room).trans (table_fund large support))
    _ ≤ (M*populations)*s := Nat.mul_le_mul_left _ power
    _ = _ := by dsimp [d];ring
  have overhead : (2*(homes*(3+3))+W)*word*T≤(2*cpu)*money := calc
    _ ≤ (2*(homes*(3+3))+W)*(cpu*h)*T := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ arch)
    _ = cpu*(12*homes*h*T+W*h*T) := by ring
    _ ≤ cpu*(money+money) := Nat.mul_le_mul_left _ (Nat.add_le_add (a.trans total) (b.trans total))
    _ = _ := by ring
  exact (paid_frontier T M d exterior rate p q W homes 3 word factor packed).trans
    ((Nat.add_le_add_left overhead _).trans_eq (by dsimp [money];ring))
end DescentCompiler.TerminalScale

end Hierarchy

end OAI
