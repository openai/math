import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace OAI
/-! # The two size budgets in one collapse step

The normalized previous size is divided by a positive power of the tree
height. The floor on that size, and the public ports, are paid for by the
independent allowance from the choice of the pin exponent.
-/

noncomputable section
namespace Hierarchy.CollapseOracle
open Filter Real

def stageHostConstant (C : ℝ) : ℕ := ⌈23*C⌉₊

private theorem smaller_power (D : ℝ) {s t : ℝ} (lt : s < t) :
    ∀ᶠ w : ℕ in atTop, D*(w:ℝ)^s ≤ (w:ℝ)^t := by
  have grows := (tendsto_rpow_atTop (sub_pos.mpr lt)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [grows.eventually_ge_atTop D,eventually_ge_atTop (1:ℕ)] with w large hw
  have pos : (0:ℝ)<w := by exact_mod_cast hw
  calc
    _ ≤ (w:ℝ)^(t-s)*(w:ℝ)^s := mul_le_mul_of_nonneg_right large (by positivity)
    _ = _ := by rw [← Real.rpow_add pos,sub_add_cancel]

/-- The asymptotic threshold depends only on the exponents, stage and
compiler constants. It is fixed before the tick, network and replication
count are chosen. The second conclusion bounds the original host records. -/
theorem stage_price (a C K : ℝ) (ha : 0<a) (ha1 : a≤1) (hC : 0≤C) (hK : 0≤K)
    (L i A' : ℕ) (hA' : a/2*L+4 ≤ A') (hlt : i<L) :
    ∀ᶠ w : ℕ in atTop, ∀ h M N e sz host Z d q : ℕ,
      1≤h → h≤w → w≤2*h → 1≤N → M=max N (10*(sz+1)) → N*w^A'≤2^w →
      0<d → 0<q → (sz:ℝ)*(w:ℝ)^(a/2*i) ≤ (q:ℝ)*(2:ℝ)^w →
      e*w^A'≤2*q*2^w → (host:ℝ)≤C*d*((M:ℝ)/(h:ℝ)^a+e) →
      (Z:ℝ)≤(1+K)*host*(h:ℝ)^(a/4) →
      (Z:ℝ)*(w:ℝ)^(a/2*(i+1:ℕ)) ≤ (d:ℝ)*q*(2:ℝ)^w ∧
        host ≤ stageHostConstant C*d*q*2^w := by
  let u : ℝ := a/2*i
  let v : ℝ := a/2*(i+1:ℕ)
  let r := a/4
  let t := r+v
  let B := (1+K)*C
  have B0 : 0≤B := mul_nonneg (by linarith) hC
  have r0 : 0≤r := by dsimp [r]; linarith
  have u0 : 0≤u := by dsimp [u]; positivity
  have cheaper : t < u+a := by dsimp [t,r,v,u]; push_cast; linarith
  have openSlack : t < A' := by
    have stages : ((i+1:ℕ):ℝ) ≤ L := by exact_mod_cast hlt
    have le := mul_le_mul_of_nonneg_left stages (by linarith : (0:ℝ)≤a/2)
    dsimp [t,r,v]
    linarith only [le,ha1,hA']
  filter_upwards [smaller_power (40*B) cheaper,smaller_power (26*B) openSlack]
    with w szRoom openRoom
  intro h M N e sz host Z d q h1 hW Wsmall N1 hM floorCost _ qpos prev ports hostCost zCost
  let T : ℝ := q*(2:ℝ)^w
  have h1R : (1:ℝ)≤h := by exact_mod_cast h1
  have wh : (h:ℝ)≤w := by exact_mod_cast hW
  have w1 := h1R.trans wh
  have wpos : (0:ℝ)<w := zero_lt_one.trans_le w1
  have wsmallR : (w:ℝ)≤2*h := by exact_mod_cast Wsmall
  have T0 : 0≤T := by dsimp [T]; positivity
  have vol : (2:ℝ)^w ≤ T := by
    dsimp [T]
    exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast qpos)
  have floorR : (N:ℝ)*(w:ℝ)^(A':ℝ) ≤ T := by
    rw [Real.rpow_natCast]
    exact (by exact_mod_cast floorCost : (N:ℝ)*(w:ℝ)^A' ≤ (2:ℝ)^w).trans vol
  have portsR : (e:ℝ)*(w:ℝ)^(A':ℝ) ≤ 2*T := by
    rw [Real.rpow_natCast]; dsimp [T]
    simpa only [mul_assoc] using (show (e:ℝ)*(w:ℝ)^A' ≤ 2*(q:ℝ)*(2:ℝ)^w by exact_mod_cast ports)
  have previous : (sz:ℝ)*(w:ℝ)^u ≤ T := prev
  have Mbound : (M:ℝ) ≤ 10*(sz:ℝ)+11*(N:ℝ) := by
    exact_mod_cast (show M ≤ 10*sz+11*N by rw [hM]; omega)
  have haOne : 1 ≤ (h:ℝ)^a := Real.one_le_rpow h1R ha.le
  have hpA : 0 < (h:ℝ)^a := zero_lt_one.trans_le haOne
  have wpA : 0 < (w:ℝ)^a := Real.rpow_pos_of_pos wpos _
  have hpower : (w:ℝ)^a ≤ 2*(h:ℝ)^a := by
    calc
      _ ≤ (2*(h:ℝ))^a := Real.rpow_le_rpow wpos.le wsmallR ha.le
      _ = (2:ℝ)^a*(h:ℝ)^a := Real.mul_rpow (by norm_num) (Nat.cast_nonneg h)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) ha1) hpA.le
  have paid : (M:ℝ)/(h:ℝ)^a+e ≤ 20*(sz:ℝ)/(w:ℝ)^a + (11*(N:ℝ)+e) := by
    have szPrice : (10*(sz:ℝ))/(h:ℝ)^a ≤ 20*(sz:ℝ)/(w:ℝ)^a := by
      apply (div_le_div_iff₀ hpA wpA).mpr
      linarith only [mul_le_mul_of_nonneg_left hpower (show 0≤10*(sz:ℝ) by positivity)]
    have cap := div_le_div_of_nonneg_right Mbound hpA.le
    rw [add_div] at cap
    linarith only [cap,szPrice,div_le_self (show 0≤11*(N:ℝ) by positivity) haOne]
  have oldCharge : (2*B)*(20*(sz:ℝ)/(w:ℝ)^a)*(w:ℝ)^t ≤ T := by
    rw [Real.rpow_add wpos u a] at szRoom
    calc
      _ = ((sz:ℝ)*(40*B*(w:ℝ)^t))/(w:ℝ)^a := by ring
      _ ≤ ((sz:ℝ)*((w:ℝ)^u*(w:ℝ)^a))/(w:ℝ)^a :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left szRoom (Nat.cast_nonneg _)) wpA.le
      _ = (sz:ℝ)*(w:ℝ)^u := by rw [← mul_assoc,mul_div_cancel_right₀ _ wpA.ne']
      _ ≤ T := previous
  have newCharge : (2*B)*(11*(N:ℝ)+e)*(w:ℝ)^t ≤ T := by
    calc
      _ = (11*(N:ℝ)+e)*(26*B*(w:ℝ)^t)/13 := by ring
      _ ≤ (11*(N:ℝ)+e)*(w:ℝ)^(A':ℝ)/13 := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left openRoom (by positivity)) (by norm_num)
      _ ≤ T := by linarith only [floorR,portsR]
  have balance : B*(20*(sz:ℝ)/(w:ℝ)^a+(11*(N:ℝ)+e))*(w:ℝ)^t ≤ T := by
    linarith only [oldCharge,newCharge]
  constructor
  · change (Z:ℝ)*(w:ℝ)^v ≤ _
    calc
      _ ≤ ((1+K)*(host:ℝ)*(h:ℝ)^r)*(w:ℝ)^v :=
        mul_le_mul_of_nonneg_right zCost (by positivity)
      _ ≤ ((1+K)*(C*d*((M:ℝ)/(h:ℝ)^a+e))*(w:ℝ)^r)*(w:ℝ)^v := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hostCost (by linarith))
          (Real.rpow_le_rpow (Nat.cast_nonneg _) wh r0) (by positivity) (by positivity)
      _ = (d:ℝ)*(B*((M:ℝ)/(h:ℝ)^a+e)*(w:ℝ)^t) := by
        dsimp only [B,t]; rw [Real.rpow_add wpos r v]; ring
      _ ≤ (d:ℝ)*(B*(20*(sz:ℝ)/(w:ℝ)^a+(11*(N:ℝ)+e))*(w:ℝ)^t) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left paid B0) (by positivity)) (Nat.cast_nonneg _)
      _ ≤ (d:ℝ)*T := mul_le_mul_of_nonneg_left balance (Nat.cast_nonneg _)
      _ = _ := by dsimp [T]; ring
  · have Aone := Real.one_le_rpow w1 (Nat.cast_nonneg A')
    have nsmall := (le_mul_of_one_le_right (Nat.cast_nonneg N) Aone).trans floorR
    have esmall := (le_mul_of_one_le_right (Nat.cast_nonneg e) Aone).trans portsR
    have ssmall := (le_mul_of_one_le_right (Nat.cast_nonneg sz) (Real.one_le_rpow w1 u0)).trans previous
    have crude : (M:ℝ)/(h:ℝ)^a+e ≤ 23*T := by
      linarith only [div_le_self (Nat.cast_nonneg M) haOne,Mbound,nsmall,esmall,ssmall]
    have cap : 23*C ≤ (stageHostConstant C:ℝ) := Nat.le_ceil _
    have hlast : (host:ℝ) ≤ (stageHostConstant C:ℝ)*d*q*(2:ℝ)^w := by
      calc
        _ ≤ C*d*(23*T) := hostCost.trans (mul_le_mul_of_nonneg_left crude (by positivity))
        _ = (23*C)*((d:ℝ)*T) := by ring
        _ ≤ (stageHostConstant C:ℝ)*((d:ℝ)*T) :=
          mul_le_mul_of_nonneg_right cap (mul_nonneg (Nat.cast_nonneg _) T0)
        _ = _ := by dsimp [T]; ring
    exact_mod_cast hlast

end Hierarchy.CollapseOracle

end
end OAI
