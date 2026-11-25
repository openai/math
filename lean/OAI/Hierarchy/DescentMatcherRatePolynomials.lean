import OAI.Hierarchy.DescentMatcherRateNumbers
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI
/-! # Polynomial bounds for the literal instruction counts of a complete ordinary date -/

namespace Hierarchy.DescentPackedColony.Phase
open DescentColonies
/-- Actual clock coefficient for the physical ordinary pass, including both
first-minimum scans and each decoded paint/key lookup, as a polynomial in
the public block radix and number of common host ports. -/
theorem factor_polynomial (k Δ : ℕ) :
    96+factor k Δ ≤ 2000*(Δ+1)*(2^k+1)^3 := by
  let r:=2^k
  have pos : 0<r := Nat.two_pow_pos _
  have small : k≤r := (Nat.lt_two_pow_self (n:=k)).le
  have count : r-1≤r := Nat.sub_le ..
  have paint : PackedWinnerRAM.work k≤1+r*(9+40*r) := by
    dsimp only [PackedWinnerRAM.work]
    rw [pow_succ]
    change 1+(r-1)*(6+(1+r*2*(6+12+2))+2)≤_
    calc
      _ ≤ 1+r*(6+(1+r*2*(6+12+2))+2) := by gcongr
      _ = _ := by ring
  unfold factor
  rw [pow_succ]
  change 96+(4+(r-1)*(4+k*(8+2*(25+56*Δ)))+200*((r-1)+1)+(8+2*(1+33*(r-1)))+
    200*(r*2+1)+(4+r*(8+2*PackedWinnerRAM.work k)))≤_
  calc
    _ ≤ 96+(4+r*(4+r*(8+2*(25+56*Δ)))+200*(r+1)+(8+2*(1+33*r))+
          200*(r*2+1)+(4+r*(8+2*(1+r*(9+40*r))))) := by gcongr
    _ ≤ 2000*(Δ+1)*(r+1)^3 := by
      ring_nf
      omega

end Hierarchy.DescentPackedColony.Phase

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentPackedColony
theorem ordinaryFactor_polynomial (k D cap K : ℕ) :
    ordinaryFactor k D cap K ≤ 5000*(1+(2^k+D+2*cap+K))^4 := by
  let r:=(2:ℕ)^k
  let level:=r+D+2*cap+K
  have powPos:=Nat.two_pow_pos k
  have radix : r≤level := by dsimp [level];omega
  have degree : D≤level := by dsimp [level];omega
  have cable : 2*cap≤level := by dsimp [level];omega
  have keys : K≤level := by dsimp [level];omega
  have choose : 96+Phase.factor k D≤2000*(level+1)*(level+1)^3 :=
    (Phase.factor_polynomial k D).trans (by change 2000*(D+1)*(r+1)^3≤_;gcongr)
  let f:=level+(level*level+level*level)
  have fields_ : fields r D (2*cap)≤f := by dsimp only [fields,f];gcongr
  have slots : r+r*(2*cap)≤level+level*level := by gcongr
  let worst:=2000*(level+1)*(level+1)^3+(8+20*level)+10*(level+2+((1+f)+(level+6)))+
    10*(2+level)+(8+level*(200*(level+1)^3+4)+4*(level+level*level))+
    54*(level+level*level)+(432+4*level)+level*(668+112*f)
  calc
    ordinaryFactor k D cap K ≤ worst := by
      dsimp only [ordinaryFactor,worst]
      change 96+Phase.factor k D+(8+20*D)+10*(r+2+((1+fields r D (2*cap))+(K+6)))+
        10*(2+K)+(8+D*(200*(D+1)^3+4)+4*(r+r*(2*cap)))+
        54*(r+r*(2*cap))+(432+4*K)+K*(668+112*fields r D (2*cap)) ≤ _
      gcongr
    _ ≤ 5000*(1+level)^4 := by dsimp only [worst,f];ring_nf;omega

end Hierarchy.DescentPacking.PackedMatch.Local.Stage

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census
open DescentPackedColony
theorem multiplier_polynomial (k D cap K work : ℕ) :
    multiplier k D cap K work≤5200*(work+1)*(1+(2^k+D+2*cap+K))^4 := by
  let level:=2^k+D+2*cap+K
  have powPos:=Nat.two_pow_pos k
  have base:=ordinaryFactor_polynomial k D cap K
  have rows : columns (2^k) cap≤level*(2+level) := by
    change 2^k*(1+(1+2*cap))≤level*(2+level)
    apply Nat.mul_le_mul <;> dsimp only [level] <;> omega
  calc
    multiplier k D cap K work ≤ 12+10*(level*(2+level))+(26+2*(level*(2+level))*(work+6))+5000*(1+level)^4 := by
      change 12+10*columns (2^k) cap+(26+2*columns (2^k) cap*(work+6))+ordinaryFactor k D cap K ≤ _
      change ordinaryFactor k D cap K≤5000*(1+level)^4 at base
      gcongr
    _ ≤ 5200*(work+1)*(1+level)^4 := by ring_nf;omega

end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill
open DescentPackedColony
theorem extra_polynomial (k D K : ℕ) :
    extraFactor k D K ≤ 1000*(1+(2^k+D+K))^3 := by
  let r:=(2:ℕ)^k
  let level:=r+D+K
  have powPos:=Nat.two_pow_pos k
  have hr : r ≤ level := by dsimp [level];omega
  have hd : D ≤ level := by dsimp [level];omega
  have hK : K ≤ level := by dsimp [level];omega
  have hj : k ≤ level := (Nat.lt_two_pow_self (n:=k)).le.trans hr
  have lower : r-1 ≤ level := (Nat.sub_le r 1).trans hr
  have total : Phase.Arena.sharedTables k D ≤ level*(level+3+4*level)+
      (1+2*level+2*level)+level*(level*(2*level)) := by
    unfold Phase.Arena.sharedTables Phase.Menu.pages
    rw [pow_succ]
    change (r-1)*(D+3+4*k)+(1+r*2+2*(r-1))+r*((r-1)*(r*2)) ≤ _
    rw [Nat.mul_comm r 2]
    gcongr
  calc
    extraFactor k D K ≤ 200+20*(level*(level+3+4*level)+
        (1+2*level+2*level)+level*(level*(2*level)))+134*level+10*level := by
      unfold extraFactor
      gcongr
    _ ≤ 1000*(1+level)^3 := by ring_nf;omega

theorem factor_polynomial (k D cap K work : ℕ) :
    Census.multiplier k D cap K work+2*extraFactor k D K ≤
      7200*(work+1)*(1+(2^k+D+2*cap+K))^4 := by
  let n:=1+(2^k+D+2*cap+K)
  have powPos:=Nat.two_pow_pos k
  have grow : 1+(2^k+D+K) ≤ n := by dsimp [n];omega
  have old:=Census.multiplier_polynomial k D cap K work
  have extra:=(extra_polynomial k D K).trans (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left grow 3))
  change Census.multiplier k D cap K work ≤ 5200*(work+1)*n^4 at old
  have positive : 1 ≤ n := by dsimp [n];omega
  have cube : n^3 ≤ n^4 := by
    calc
      n^3 = n^3*1 := by simp
      _ ≤ n^3*n := Nat.mul_le_mul_left _ positive
      _ = n^4 := by ring
  have weighted : n^4 ≤ (work+1)*n^4 := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  change _ ≤ 7200*(work+1)*n^4
  nlinarith only [old,extra,cube,weighted]

end Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill

end OAI
