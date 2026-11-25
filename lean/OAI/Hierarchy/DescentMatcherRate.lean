import OAI.Hierarchy.DescentMatcherChargeFactor
import OAI.Hierarchy.DescentMatcherCompleteTariff
import OAI.Hierarchy.DescentPrivateDonorUniform

namespace OAI
/-! # A common schedule exponent for the chosen matcher and count publication -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill
open DescentCompiler.TerminalScale

theorem matchCountRate_poly (k D cap K bound : ℕ) :
    matchCountRate k D cap K bound ≤
      200000*(23+bound)*(1+(2^k+D+2*cap+K+bound))^4 := by
  let n:=1+(2^k+D+2*cap+K+bound)
  have radixPos := Nat.two_pow_pos k
  have nPos : 0<n:=by dsimp [n];omega
  have kn : 1+K≤n:=by dsimp [n];omega
  have nFour : n≤n^4 := by
    calc
      n = n^1:=by simp
      _ ≤ n^4:=Nat.pow_le_pow_right nPos (by decide)
  have ctl:=controlFactor_polynomial k D cap K bound
  have base:=factor_polynomial k D cap K (max 22 bound)
  have enlarge:=Nat.pow_le_pow_left (show 1+(2^k+D+2*cap+K)≤n by dsimp [n];omega) 4
  have expr : max 22 bound+1≤23+bound :=by omega
  have old : Census.multiplier k D cap K (max 22 bound)+2*extraFactor k D K≤7200*(23+bound)*n^4 :=
    base.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ expr) enlarge)
  change controlFactor k D cap K bound≤30000*n^4 at ctl
  change 5*_+2*(controlFactor k D cap K bound+2000*(1+K))≤200000*(23+bound)*n^4
  nlinarith only [old,ctl,kn.trans nFour,Nat.zero_le (bound*n^4),Nat.zero_le (n^4)]

theorem matchCountRate_scale {k D cap bound J s e : ℕ}
    (date : donorGrade (2^k) D cap≤ scale J s) (input : bound≤ scale J e) :
    matchCountRate k D cap (2^(k+1)) bound≤ matchingConstant*scale J ((s+e)*5) := by
  let r:=2^k
  let n:=max r (max (D+1) (max cap (2*r)))
  have oneR : 0<r:=Nat.two_pow_pos _
  have rad : r≤n:=le_max_left ..
  have deg : D+1≤n:=(le_max_left ..).trans (le_max_right ..)
  have capN : cap≤n:=(le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..))
  have nPos:=oneR.trans_le rad
  have n4 : n≤n^4 :=by simpa only [pow_one] using Nat.pow_le_pow_right nPos (by decide : 1≤4)
  have dom : n≤donorGrade r D cap:=by
    change n≤800*n^4+_+_+_
    omega
  let v:=scale J (s+e)
  have liftScale (a b : ℕ) (h : a≤b) : scale J a≤ scale J b :=
    Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.mul_le_mul_right _ h)
  have small : n≤v :=dom.trans (date.trans (liftScale _ _ (Nat.le_add_right ..)))
  have reads : bound≤v :=input.trans (liftScale _ _ (Nat.le_add_left ..))
  have vPos : 0<v:=Nat.two_pow_pos _
  have census : 1+(2^k+D+2*cap+2^(k+1)+bound)≤8*v:=by
    rw [pow_succ]
    change 1+(r+D+2*cap+r*2+bound)≤_
    omega
  have work : 23+bound≤24*v:=by omega
  have power : v^5=scale J ((s+e)*5):=by
    unfold v scale
    rw [←pow_mul]
    congr 1
    ring
  calc
    _ ≤ 200000*(23+bound)*(1+(2^k+D+2*cap+2^(k+1)+bound))^4:=matchCountRate_poly ..
    _ ≤ 200000*(24*v)*(8*v)^4:=Nat.mul_le_mul (Nat.mul_le_mul_left _ work) (Nat.pow_le_pow_left census 4)
    _ = _:=by rw [←power];unfold matchingConstant;ring

end Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill

end OAI
