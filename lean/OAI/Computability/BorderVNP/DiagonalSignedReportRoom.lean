import OAI.Computability.BorderVNP.DiagonalSignedProgramMass
import OAI.Computability.BorderVNP.DiagonalJointWords

/-! # Numeric report words and private call bounds on the selected processor -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Cover BorderVNP.Epoch Packing TeamScales Filter
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {a extra E deg Q A B j : ℕ} {s : EpochScales S a extra}

set_option maxHeartbeats 1000000 in
/-- On the common diagonal schedule the cell uses its whole physical word
for each reported multiplicity. The genuine aggregated local storage and the
wide gadget digits fit together in the quarter-power private input. -/
theorem JointSchedule.eventually_signed_report_room (b : JointSchedule s (E+1) deg Q A B j)
    (gadgets coefficient : ℕ) (degree : E+2 ≤ deg) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let w := b.physical.word n
      let M := TeamScales.width n (1/5)
      let ext := TeamScales.width n (1/4)
      0<w ∧ w≤M ∧ M<2^w ∧ gadgets≤M+1 ∧ 3*M+gadgets*w≤ext ∧
        w≤(logWidth r n+1)^(E+2) ∧
        ∀ mass seed Z : ℕ, mass≤M → seed≤M →
          Z ≤ max seed (max (coefficient*(mass+1)) (max 1 (15*mass))) →
          3*M+Z≤4*(M+ext+1)^3 := by
  have big := eventually_le_rounded_width (show (0:ℝ)<1/5 by norm_num) (by norm_num)
    (by norm_num : (0:ℝ)<1) ((max gadgets (max coefficient 15) : ℕ):ℝ)
  have quarter := eventually_le_rounded_width (show (1:ℝ)/5<1/4 by norm_num) (by norm_num) (by norm_num : (0:ℝ)<1) (3+(gadgets:ℝ))
  filter_upwards [b.eventually_lengths 0,b.eventually_word_capacity 1 1,big,quarter,eventually_ge_atTop 1] with n h space large extent hn
  intro r w M ext
  let L := logWidth r n
  have hr : 1 ≤ r := stretch_one ..
  have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hL : 1 ≤ L := by
    exact (Nat.size_pos.mpr hn).trans_le (CellMacro.Generator.size_le_logWidth n r hr)
  have total : max gadgets (max coefficient 15) ≤ M := by
    exact_mod_cast (by simpa only [Real.rpow_zero,mul_one,one_mul] using large :
      ((max gadgets (max coefficient 15):ℕ):ℝ) ≤ (TeamScales.width n (1/5):ℝ))
  have formula : w=L^(E+2) := (b.sizes hn).2.2.1
  have power : w≤M := by
    apply Nat.le_floor
    calc
      (w:ℝ) = (L:ℝ)^(E+2) := by exact_mod_cast formula
      _ ≤ (L:ℝ)^deg := pow_le_pow_right₀ (by exact_mod_cast hL) degree
      _ ≤ (n:ℝ)^((s.τ:ℝ)/2000) := h.logs
      _ ≤ (n:ℝ)^(1/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hn' (by linarith [s.tau_small,s.alpha_small])
  have Mle : M ≤ n := Nat.floor_le_of_le ((Real.rpow_le_rpow_of_exponent_le hn'
    (by norm_num : (1/5:ℝ) ≤ 1)).trans_eq (Real.rpow_one _))
  have wide : M < 2^w :=
    (Mle.trans (Nat.le_succ_of_le (Nat.le_mul_of_pos_left n hr))).trans_lt (by simpa only [one_mul,pow_one] using space.2.2.1)
  have positive : 0<w := by rw [formula]; exact Nat.pow_pos hL
  refine ⟨positive,power,wide,by omega,?_,?_,?_⟩
  · have limit : (3+gadgets)*M ≤ ext := by
      exact_mod_cast (calc
        (3+(gadgets:ℝ))*(M:ℝ) ≤ (3+gadgets)*(n:ℝ)^(1/5:ℝ) :=
          mul_le_mul_of_nonneg_left (Nat.floor_le (Real.rpow_nonneg (by positivity) _)) (by positivity)
        _ ≤ (ext:ℝ) := by simpa only [one_mul] using extent)
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left gadgets power) _).trans ((by ring : 3*M+gadgets*M=(3+gadgets)*M).le.trans limit)
  · rw [formula]; exact Nat.pow_le_pow_left (Nat.le_succ L) _
  · intro mass seed Z hm hs hz
    have cf : coefficient ≤ M := by omega
    have above : 15 ≤ M := by omega
    have product := Nat.mul_le_mul cf (Nat.succ_le_succ hm)
    have fifteen := Nat.mul_le_mul above hm
    have one : 1 ≤ M*(M+1) := by nlinarith
    have sum : Z≤M*(M+1) := hz.trans (max_le (by nlinarith) (max_le product (max_le one (by nlinarith))))
    nlinarith [Nat.zero_le ext, Nat.zero_le M, Nat.zero_le (M^2*ext), Nat.zero_le (ext^2*M)]

end Diagonal

end BorderVNP
end Computability
end OAI
