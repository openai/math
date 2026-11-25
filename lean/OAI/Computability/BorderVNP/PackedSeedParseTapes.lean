import OAI.Computability.BorderVNP.PackedSignedSeedDecay
import OAI.Computability.BorderVNP.PackedSeedBoxRate

/-! # Actual padded original tapes on any batch meeting the parse volume

The private description bound follows directly from the given one-copy
verifier volume and the rounded initial cover. Thus it applies on a joint
schedule whose processor count has already been selected.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid

open Cover CoverScale TeamScales Filter Diagonal.ExternalSew
open private seedTape_le from OAI.Computability.BorderVNP.PackedSeedTapeRate
open private box_bounds from OAI.Computability.BorderVNP.PackedSeedBoxRate
open private log_cube_le from OAI.Computability.BorderVNP.PackedSignedSeedDecay

/-- Pay both the routed channel and its complete fixed-width private tape
on the real cover at every batch with the stated verifier-volume bound. -/
theorem eventually_seed_stored_of_parse {τ : ℝ} (ht : 0 < τ) (hs : τ < 1/100)
    (q degree head : ℕ) [NeZero q] :
    ∀ᶠ n : ℕ in atTop, ∀ (r d : ℕ), 1 ≤ r →
      (GridHosts.tileCount q d:ℝ) ≤ r*(n:ℝ)^(9/10:ℝ) →
      (r:ℝ)*(n:ℝ)^(9/10:ℝ)/factor (Fin q) < GridHosts.tileCount q d →
      (batchVolume n r:ℝ) ≤ volume τ r n →
      let H := seedChannelWidth n r q d
      let cap := seedBoxCapacity n r q d degree
      let dB := seedDescriptionWidth n r q d (head*logWidth r n) (BottomGridBank.bodyBudget cap)
      cap ≤ n ∧ (1+H+dB:ℝ) ≤ (n:ℝ)^(1/10+τ/5) := by
  let A : ℝ := (96*(4*q+1)+1:ℝ)*factor (Fin q)
  let B := max head (4*(1+19*(11+2*degree)))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have capRoom := eventually_rpow_gap (by linarith : 1/10+τ/10 < 1) ((11+2*degree:ℝ)*A)
  have pay := eventually_rpow_gap (by linarith : 1/10+τ/10+τ/20 < 1/10+τ/5) ((1+9*B:ℝ)*(A+1))
  filter_upwards [capRoom,pay,eventually_ge_atTop 8] with n hc hp hn
  intro r d hr small large parse H cap dB
  have hn1 : 1 ≤ n := by omega
  have realn : 1 ≤ (n:ℝ) := by exact_mod_cast hn1
  have pos := zero_lt_one.trans_le realn
  let L := logWidth r n
  have hlog : (L:ℝ)^3 ≤ (n:ℝ)^(τ/20) := log_cube_le hn1 hr parse
  have hL : (L:ℝ) ≤ (n:ℝ)^(τ/20) := by
    have one : 1 ≤ L := by
      dsimp only [L]; rw [Shortening.PublicCapacity.public_logWidth]
      exact (show 1=Nat.clog 2 2 by decide).le.trans (Nat.clog_mono_right 2 (by nlinarith))
    have cmp : (L:ℝ) ≤ (L:ℝ)^3 := by
      simpa only [pow_one] using pow_le_pow_right₀ (by exact_mod_cast one : 1 ≤ (L:ℝ)) (by decide : 1 ≤ 3)
    exact cmp.trans hlog
  have hH : (H:ℝ) ≤ A*(n:ℝ)^(1/10+τ/10) := by
    have g := seedChannelWidth_le (q := q) hn1 hr ht.le small large parse
    calc
      _ ≤ A*(n:ℝ)^(1/10+τ/20)*(L:ℝ)^3 := g
      _ ≤ A*(n:ℝ)^(1/10+τ/20)*(n:ℝ)^(τ/20) := by gcongr
      _ = _ := by rw [mul_assoc,←Real.rpow_add pos]; congr 2; ring
  have capN : cap ≤ n := by
    have capH : (cap:ℝ) ≤ (11+2*degree:ℝ)*H := by exact_mod_cast seedBoxCapacity_le n r q d degree
    have h := capH.trans (mul_le_mul_of_nonneg_left hH (by positivity))
    rw [Real.rpow_one] at hc
    have bound : (cap:ℝ) ≤ n := h.trans (by simpa only [mul_assoc] using hc)
    exact_mod_cast bound
  have body : BottomGridBank.bodyBudget cap ≤ B*(H+1)*L^1 := by
    rw [pow_one]
    exact (box_bounds hn hr capN).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le_max_right ..)))
  have hhead : head*L ≤ B*L^1 := by rw [pow_one]; exact Nat.mul_le_mul_right _ (le_max_left ..)
  have tape : (dB:ℝ) ≤ 9*B*(H+1)*(L:ℝ) := by
    have h := seedTape_le n r q d (head*L) (BottomGridBank.bodyBudget cap) B L 1 hhead body
    rw [pow_one] at h
    exact_mod_cast h
  have h1 := Real.one_le_rpow realn (show 0 ≤ 1/10+τ/10 by linarith)
  have L1 := Real.one_le_rpow realn (show 0 ≤ τ/20 by linarith)
  have hplus : (H:ℝ)+1 ≤ (A+1)*(n:ℝ)^(1/10+τ/10) := by linarith only [hH,h1]
  have exactSum : 1+H+dB ≤ (1+9*B:ℝ)*((A+1)*(n:ℝ)^(1/10+τ/10))*(n:ℝ)^(τ/20) := by
    have t := tape.trans (mul_le_mul (mul_le_mul_of_nonneg_left hplus (by positivity)) hL (by positivity) (by positivity))
    have u := hplus.trans (le_mul_of_one_le_right (by positivity) L1)
    linarith only [t,u]
  refine ⟨capN,exactSum.trans ?_⟩
  calc
    _ = ((1+9*B:ℝ)*(A+1))*(n:ℝ)^(1/10+τ/10+τ/20) := by rw [Real.rpow_add pos (1/10+τ/10) (τ/20)]; ring
    _ ≤ _ := hp

end Packing.DeckGrid

end BorderVNP
end Computability
end OAI
