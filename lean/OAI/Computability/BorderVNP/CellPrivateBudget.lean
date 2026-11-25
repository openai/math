import OAI.Computability.BorderVNP.TeamScales
import OAI.Computability.BorderVNP.RoutingISACompactFrame

/-! # Private cell input and execution bounds at the physical word interface

The expanded incidence weight and the delivered input bits have different exponents in
Proposition 7.2. A quadratic contribution in the incidence weight still fits the private
input allowance. Fixed polynomial costs in binary index lengths are absorbed by the choice
of the batch exponent.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open Filter TeamScales RoutingISA

/-- A nonempty word width uses at most one physical word per framed input bit. -/
theorem packed_words_le_framed {w : ℕ} (hw : 0 < w) (payload : List Bool) :
    (CompactFrame.pack w payload).length ≤ 2*payload.length+1 := by
  rw [CompactFrame.length_pack, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hw]
  let l := 2*payload.length+1
  change l+w-1 < l.succ*w
  have := Nat.mul_le_mul_left l (show 1 ≤ w from hw)
  rw [Nat.mul_one] at this
  rw [Nat.succ_mul]
  omega

private theorem logWidth_pos {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r) : 1 ≤ logWidth r n := by
  have h : 2 ≤ 2*(n:ℝ)*r := by
    have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast hn
    have hr' : 1 ≤ (r:ℝ) := by exact_mod_cast hr
    nlinarith
  have : (1:ℝ) ≤ Real.logb 2 (2*(n:ℝ)*r) := by
    rw [← Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
    exact (Real.logb_le_logb (by norm_num) (by norm_num) (by linarith)).mpr h
  have hceil : (1:ℝ) ≤ logWidth r n := this.trans (Nat.le_ceil _)
  exact_mod_cast hceil

private theorem compact_scale {M E n : ℕ} (hn : 1 ≤ n) (hM : M ≤ width n (1/5))
    (hE : E ≤ width n (1/4)) :
    ((M:ℝ)+1)^2+E+1 ≤ 6*(n:ℝ)^(2/5:ℝ) ∧
      ((M:ℝ)+E+1)^96 ≤ 3^96*(n:ℝ)^(24:ℝ) := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos := zero_lt_one.trans_le hn'
  have hm : (M:ℝ) ≤ (n:ℝ)^(1/5:ℝ) :=
    (Nat.cast_le.mpr hM).trans (Nat.floor_le (Real.rpow_nonneg hnpos.le _))
  have he : (E:ℝ) ≤ (n:ℝ)^(1/4:ℝ) :=
    (Nat.cast_le.mpr hE).trans (Nat.floor_le (Real.rpow_nonneg hnpos.le _))
  have h1 := Real.one_le_rpow hn' (by norm_num : (0:ℝ) ≤ 1/5)
  have h25 := Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (1/5:ℝ) ≤ 1/4)
  have h40 := Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (1/4:ℝ) ≤ 2/5)
  constructor
  · have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ M+1)
      (show (M:ℝ)+1 ≤ 2*(n:ℝ)^(1/5:ℝ) by linarith) 2
    rw [mul_pow, ← Real.rpow_natCast ((n:ℝ)^(1/5:ℝ)) 2, ← Real.rpow_mul hnpos.le] at h
    norm_num at h
    linarith
  · have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ M+E+1)
      (show (M:ℝ)+E+1 ≤ 3*(n:ℝ)^(1/4:ℝ) by linarith) 96
    rwa [mul_pow, ← Real.rpow_natCast ((n:ℝ)^(1/4:ℝ)) 96, ← Real.rpow_mul hnpos.le,
      show (1/4:ℝ)*(96:ℕ) = 24 by norm_num] at h

/-- One batch exponent works for every fixed coefficient. The work input includes generation,
the final reversal of the bytecode, and the interpreter. The conclusion accounts for the
framed word decoder and the factor of two for native tape steps as well. -/
theorem eventually_private_budget (D : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A : ℕ, ∀ᶠ n : ℕ in atTop, ∀ r M E w : ℕ,
      1 ≤ r → (r:ℝ) ≤ 2^((n:ℝ)^ω) → M ≤ width n (1/5) → E ≤ width n (1/4) →
      0 < w → w ≤ n → ∀ (payload : List Bool) (work : ℕ),
      payload.length ≤ A*((M+1)^2+E+1)*(logWidth r n+1)^D →
      work ≤ A*(M+E+1)^96*(logWidth r n+1)^D →
      (CompactFrame.pack w payload).length ≤ width n (1/2) ∧
      2*(3*((CompactFrame.pack w payload).length*w)+work) ≤ n^25 := by
  obtain ⟨ω,hω,hp⟩ := exists_polylog_budget D (by norm_num : (0:ℝ) < 1/100)
  refine ⟨ω,hω,fun A => ?_⟩
  let c : ℝ := A*2^D
  have hs := eventually_rpow_gap (by norm_num : (2/5:ℝ)+1/100 < 1/2) (12*c+1)
  have ht := eventually_rpow_gap (by norm_num : (24:ℝ)+1/100 < 25) (6+2*c*3^96)
  filter_upwards [hp,hs,ht,eventually_ge_atTop 1] with n hp hs ht hn
  intro r M E w hr hrω hM hE hw hwn payload work hpayload hwork
  have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hnpos := zero_lt_one.trans_le hn'
  have hl : (1:ℝ) ≤ logWidth r n := by exact_mod_cast logWidth_pos hn hr
  have hlog : ((logWidth r n:ℝ)+1)^D ≤ 2^D*(n:ℝ)^(1/100:ℝ) := by
    calc _ ≤ (2*(logWidth r n:ℝ))^D := pow_le_pow_left₀ (by positivity) (by linarith) _
         _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_left (hp r hr hrω) (by positivity)
  obtain ⟨hcompact,hrun⟩ := compact_scale hn hM hE
  have hpl : (payload.length:ℝ) ≤ (A:ℝ)*(((M:ℝ)+1)^2+E+1)*((logWidth r n:ℝ)+1)^D := by
    exact_mod_cast hpayload
  have hc : (payload.length:ℝ) ≤ 6*c*(n:ℝ)^((2/5:ℝ)+1/100) := by
    calc _ ≤ (A:ℝ)*(6*(n:ℝ)^(2/5:ℝ))*(2^D*(n:ℝ)^(1/100:ℝ)) := hpl.trans (by gcongr)
         _ = _ := by rw [Real.rpow_add hnpos]; dsimp [c]; ring
  have hwds : (CompactFrame.pack w payload).length ≤ width n (1/2) := by
    apply (packed_words_le_framed hw payload).trans (Nat.le_floor ?_)
    push_cast
    have h1 := Real.one_le_rpow hn' (by norm_num : (0:ℝ) ≤ 2/5+1/100)
    linarith only [hc,hs,h1]
  refine ⟨hwds,?_⟩
  have hwds' : (CompactFrame.pack w payload).length ≤ n := by
    apply hwds.trans
    have := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (1/2:ℝ) ≤ 1))
    simpa only [width, Real.rpow_one, Nat.floor_natCast] using this
  have hwl : (work:ℝ) ≤ (A:ℝ)*((M:ℝ)+E+1)^96*((logWidth r n:ℝ)+1)^D := by exact_mod_cast hwork
  have hc' : (work:ℝ) ≤ c*3^96*(n:ℝ)^((24:ℝ)+1/100) := by
    calc _ ≤ (A:ℝ)*(3^96*(n:ℝ)^(24:ℝ))*(2^D*(n:ℝ)^(1/100:ℝ)) := hwl.trans (by gcongr)
         _ = _ := by rw [Real.rpow_add hnpos]; dsimp [c]; ring
  have hwords : ((CompactFrame.pack w payload).length:ℝ)*w ≤ (n:ℝ)^((24:ℝ)+1/100) := by
    calc _ ≤ (n:ℝ)^2 := by rw [pow_two]; exact mul_le_mul (Nat.cast_le.mpr hwds')
                                                (Nat.cast_le.mpr hwn) (by positivity) (by positivity)
         _ ≤ _ := by rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hn' (by norm_num)
  rw [show (25:ℝ) = (25:ℕ) by norm_num, Real.rpow_natCast] at ht
  exact_mod_cast (show (2:ℝ)*(3*(((CompactFrame.pack w payload).length:ℝ)*w)+work) ≤ (n:ℝ)^25 by
    linarith only [ht,hwords,hc'])

end CellSparse

end BorderVNP
end Computability
end OAI
