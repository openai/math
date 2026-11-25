import OAI.Hierarchy.DescentTerminalCalibratedRowArithmetic

namespace OAI
/-! # The original paired public header and paid row bank in the terminal open invoice -/
namespace Hierarchy.DescentSixParty
open DescentCompiler.TerminalScale DescentTerminalGraphVolume DescentTerminalCompiledPrefix.AddressPlan
section Price
variable (T M copies s E rate p q W homes h w factor blocks H mult : ℕ)
local notation "d" => copies*s
local notation "total_" => integralFrontier T M d E rate
local notation "budget" => rowBudget p q W total_ (d*E) homes 3
local notation "coveredRows" => bought budget W
local notation "fund" => d*(M+T*E)
local notation "ρ" => 6*(32*factor)*(3+4*rate)+2*factor

/-- Price the physical header, paid rows and archive size on the open original host.
The header is allowed its full computed raw-word prefix in addition to the paid row pool. -/
theorem preflight_open_pages (headers paid : ℕ) (positive : 0<W) (room : W≤2^(h/2))
    (large : 10≤h) (support : 2^h≤2*(M*copies)) (width : T≤ s)
    (arch : w+1≤factor*h) (packed : h≤32*(q*p))
    (positions : (4+(homes+1)*(26+234*blocks))*h*T≤M*d)
    (frozen : H*mult*h*T≤M*d)
    (headerCount : headers≤ coveredRows+(total_/(q*p)+1)) (paidCount : paid≤coveredRows) :
    ((2^(h/2)+H*mult)*(w+1)+(paid+headers)*(w+1))*T≤(2*factor+6*ρ)*fund := by
  have internal : M*d≤fund := by rw [Nat.mul_add,Nat.mul_comm M];omega
  have half : 2^(h/2)*h*T≤M*d := by
    calc
      _ ≤ (M*copies)*s := Nat.mul_le_mul (table_fund large support) width
      _ = _ := by ring
  have basic (v : ℕ) (hv : v*h*T≤M*d) : v*(w+1)*T≤factor*fund := by
    calc
      _ ≤ v*(factor*h)*T := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ arch)
      _ = factor*(v*h*T) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (hv.trans internal)
  have packedWidth : w+1≤(32*factor)*(q*p) := by
    calc
      _ ≤ factor*(32*(q*p)) := arch.trans (Nat.mul_le_mul_left _ packed)
      _ = _ := by ring
  have base := covered_bank T M copies s E rate p q W homes h (w+1) (32*factor) factor blocks
    room large support width packedWidth arch positions
  have cap := cap_both (n:=budget) positive (by unfold rowBudget;omega)
  have divided : total_/(q*p)≤(3*(2*total_+d*E))/(q*p) := Nat.div_le_div_right (by omega)
  have raw : total_/(q*p)+1≤budget := by unfold rowBudget;omega
  have rows : paid+headers≤6*budget := by omega
  have weighted : (paid+headers)*(w+1)*T≤6*(ρ*fund) := by
    calc
      _ ≤ (6*budget)*(w+1)*T := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ rows)
      _ = 6*(budget*(w+1)*T) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ base
  calc
    _ = 2^(h/2)*(w+1)*T+(H*mult)*(w+1)*T+(paid+headers)*(w+1)*T := by ring
    _ ≤ factor*fund+factor*fund+6*(ρ*fund) := Nat.add_le_add (Nat.add_le_add (basic _ half) (basic _ frozen)) weighted
    _ = _ := by ring
end Price
end Hierarchy.DescentSixParty

end OAI
