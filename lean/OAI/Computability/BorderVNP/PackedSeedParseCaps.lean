import OAI.Computability.BorderVNP.PackedSeedParseTapes
import OAI.Computability.BorderVNP.PackedSeedSelectedCaps

/-! # Sewn cell thresholds and original-tape capacity at the prescribed batch length -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid

open Cover CoverScale TeamScales Filter Diagonal.ExternalSew

set_option maxHeartbeats 1500000 in
/-- All original metadata and every chosen terminal charge fit at the same
batch as the prewired verifier, using its true cover bounds and input volume. -/
theorem eventually_seed_actual_caps_of_parse {α τ : ℝ} (ha : 0<α) (small : α<1/1000)
    (ht : 0<τ) (tiny : τ<α/100) {C : ℕ} (factorPos : 1≤C) (growth : τ*Real.logb 2 C ≤ 2*α)
    (q degree headerFactor : ℕ) [NeZero q] :
    ∀ᶠ n : ℕ in atTop, ∀ r depth : ℕ, 1≤r →
      let V := GridHosts.tileCount q depth
      (V:ℝ) ≤ r*(n:ℝ)^(9/10:ℝ) → (r:ℝ)*(n:ℝ)^(9/10:ℝ)/factor (Fin q)<V →
      (batchVolume n r:ℝ) ≤ volume τ r n →
      let H := seedChannelWidth n r q depth
      let cap := seedBoxCapacity n r q depth degree
      let dB := seedDescriptionWidth n r q depth (headerFactor*logWidth r n) (BottomGridBank.bodyBudget cap)
      let b := width n α
      let T := epochs τ n
      let M := C^T*baseMass degree cap H b dB
      5*b*(C^T*seedPublicBase degree) ≤ width n (1/100) ∧ 7*M ≤ width n (1/5) ∧
        dB ≤ literal α n/2 ∧ ∀ fan, fan^T*V*dB ≤ teams α τ fan n*r*(literal α n/2) := by
  let β := 1/10+τ/5
  let A := seedPublicBase degree+12+810489*(11+2*degree)+(2*degree+1)+1
  have sizes := eventually_seed_stored_of_parse ht (by linarith) q degree headerFactor
  have pub := eventually_le_rounded_width (show α+2*α < 1/100 by linarith) (by norm_num)
    (by norm_num : (0:ℝ)<1) (5*seedPublicBase degree:ℝ)
  have mass := eventually_le_rounded_width (show 2*α+α+β < 1/5 by dsimp [β]; linarith)
    (by norm_num) (by norm_num : (0:ℝ)<1) (7*A:ℝ)
  have lit : 0<1-α/3 := by linarith
  have single := eventually_le_rounded_width (show β<1-α/3 by dsimp [β]; linarith) lit
    (by norm_num : (0:ℝ)<1/2) 1
  have copies := eventually_le_rounded_width (show α/2<α by linarith) ha (by norm_num : (0:ℝ)<1) 1
  have half := eventually_le_rounded_width (show 9/10+β-α/2<1-α/3 by dsimp [β]; linarith) lit
    (by norm_num : (0:ℝ)<1/4) 1
  have two := eventually_le_rounded_width (show 0<1-α/3 by linarith) lit (by norm_num : (0:ℝ)<1) 2
  filter_upwards [sizes,pub,mass,single,copies,half,two,eventually_ge_atTop 1] with n nsize np nm ns nb nh nt hn
  intro r d hr V hv large parse H cap dB b T M
  have hn' : 1≤(n:ℝ) := by exact_mod_cast hn
  have hn0 := zero_lt_one.trans_le hn'
  have hC : 1≤(C:ℝ) := by exact_mod_cast factorPos
  have hfactor : ((C^T:ℕ):ℝ) ≤ (n:ℝ)^(2*α) := by exact_mod_cast epoch_growth_le hC hn ht.le growth
  have hb : (b:ℝ)≤(n:ℝ)^α := Nat.floor_le (by positivity)
  have one : 0<b := Nat.le_floor (by simpa using Real.one_le_rpow hn' ha.le)
  have store : 1+H+dB ≤ (n:ℝ)^β := (nsize r d hr hv large parse).2
  have tape : (dB:ℝ)≤(n:ℝ)^β := by linarith only [store,Nat.cast_nonneg (α:=ℝ) H]
  have raw := (baseMass_scale n r q d degree b dB one).2
  have data : (baseMass degree cap H b dB:ℝ) ≤ A*b*(1+H+dB) := by exact_mod_cast raw
  have htwoR : (2:ℝ)≤literal α n := by simpa only [literal,Real.rpow_zero,mul_one,one_mul] using nt
  have htwo : 2≤literal α n := by exact_mod_cast htwoR
  have hhalf : (literal α n:ℝ)/4 ≤ ((literal α n/2:ℕ):ℝ) := by
    apply (div_le_iff₀ (by norm_num)).mpr
    exact_mod_cast (show literal α n ≤ literal α n/2*4 by omega)
  have factor' : (C:ℝ)^T ≤ (n:ℝ)^(2*α) := by exact_mod_cast hfactor
  refine ⟨?_,?_,?_,?_⟩
  · apply (Nat.cast_le (α:=ℝ)).mp
    push_cast
    calc
      _ ≤ 5*(n:ℝ)^α*((n:ℝ)^(2*α)*seedPublicBase degree) := by gcongr
      _ = (5*seedPublicBase degree:ℝ)*(n:ℝ)^(α+2*α) := by rw [Real.rpow_add hn0]; ring
      _ ≤ _ := by simpa only [one_mul] using np
  · apply (Nat.cast_le (α:=ℝ)).mp
    dsimp only [M]
    push_cast
    calc
      _ ≤ 7*((n:ℝ)^(2*α)*((A:ℝ)*(n:ℝ)^α*(n:ℝ)^β)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul factor' (data.trans (mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity)) store (by positivity) (by positivity))) (by positivity) (by positivity)
      _ = (7*A:ℝ)*(n:ℝ)^(2*α+α+β) := by rw [Real.rpow_add hn0 (2*α+α) β,Real.rpow_add hn0 (2*α) α]; ring
      _ ≤ _ := by simpa only [one_mul] using nm
  · apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
    have fit : (n:ℝ)^β ≤ (1/2:ℝ)*literal α n := by simpa only [literal,one_mul] using ns
    exact_mod_cast (show (dB:ℝ)*2 ≤ literal α n by linarith only [tape,fit])
  · intro fan
    have ncopy : (n:ℝ)^(α/2) ≤ b := by simpa only [one_mul] using nb
    have ntail : (n:ℝ)^(9/10+β-α/2) ≤ ((literal α n/2:ℕ):ℝ) :=
      (show (n:ℝ)^(9/10+β-α/2) ≤ (literal α n:ℝ)/4 by unfold literal; linarith only [nh]).trans hhalf
    have bound : V*dB ≤ r*(b*(literal α n/2)) := by
      apply (Nat.cast_le (α:=ℝ)).mp
      push_cast
      calc
        _ ≤ ((r:ℝ)*(n:ℝ)^(9/10:ℝ))*(n:ℝ)^β := by gcongr
        _ = (r:ℝ)*((n:ℝ)^(α/2)*(n:ℝ)^(9/10+β-α/2)) := by
          rw [←Real.rpow_add hn0 (α/2) (9/10+β-α/2),show α/2+(9/10+β-α/2)=9/10+β by ring,Real.rpow_add hn0 (9/10) β]; ring
        _ ≤ _ := by gcongr
    simpa only [teams,mul_comm,mul_left_comm,mul_assoc] using Nat.mul_le_mul_left (fan^T) bound

end Packing.DeckGrid

end BorderVNP
end Computability
end OAI
