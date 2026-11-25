import OAI.Computability.BorderVNP.DiagonalExternalSewPhysicalVolume
import OAI.Computability.BorderVNP.PackedCoverScale
import OAI.Computability.BorderVNP.PackedInitialLayout
import OAI.Computability.BorderVNP.PackedPotential

/-! # Exterior interval widths for the actual initial product cover

For the team count and initial depth chosen in §7.1, a consecutive site
block fits inside either the literal or a single physical exterior field.
The threshold is uniform over every positive processor count.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Filter Packing TeamScales Crossing
open scoped Classical

variable (I : Type) [Fintype I] [Nonempty I]

private theorem eventually_blockWidth (e : ℝ) (he : 1/10 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r →
      let V := CoverScale.sites I (CoverScale.initialDepth I r n)
      blockWidth (r*n) V ≤ width n e := by
  let F := CoverScale.factor I
  have hF : 0 < (F : ℝ) := by exact_mod_cast (zero_lt_one.trans (CoverScale.one_lt_factor I))
  have hslack := eventually_le_rounded_width he (by linarith) (show (0 : ℝ) < 1 by norm_num) (F : ℝ)
  have hbase := eventually_rpow_gap (show (0 : ℝ) < 9/10 by norm_num) (CoverScale.sites I 1 : ℝ)
  filter_upwards [hslack,hbase,eventually_ge_atTop 1] with n hw hb hn
  simp only [one_mul] at hw
  simp only [Real.rpow_zero,mul_one] at hb
  intro r hr V
  have hr' : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hn)
  have hb' := hb.trans (le_mul_of_one_le_left (Real.rpow_nonneg hn'.le _) hr')
  have hv := (CoverScale.initial_sites I hb').1
  change (r : ℝ)*(n : ℝ)^(9/10 : ℝ)/F < (V : ℝ) at hv
  have hV : 0 < V := Fintype.card_pos
  apply (ceilDiv_le_iff_le_mul hV).mpr
  apply Nat.cast_le (α := ℝ) |>.mp
  simp only [Nat.cast_mul]
  calc
    (r : ℝ)*n = ((r : ℝ)*(n : ℝ)^(9/10 : ℝ)/F) * ((F : ℝ)*(n : ℝ)^(1/10 : ℝ)) := by
      rw [div_mul_eq_mul_div,mul_div_assoc]
      field_simp
      rw [← Real.rpow_add hn']
      norm_num
    _ ≤ (V : ℝ)*(width n e : ℝ) := mul_le_mul hv.le hw (by positivity) (by positivity)

/-- Uniform site-block hypotheses for the exact ceiling allocation, for either
all processor slots or any positive retained prefix no larger than `r*n`. -/
theorem eventually_block_fields {α τ : ℝ} {K : ℕ} (hα : 0 < α) (hα' : α < 1/1000)
    (hτ : 0 ≤ τ) (hτ' : τ < α/100) (hK : 1 ≤ K) (fan : τ * Real.logb 2 K ≤ α) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → ∀ slots : ℕ, 0 < slots → slots ≤ r*n →
      let V := CoverScale.sites I (CoverScale.initialDepth I r n)
      let g := blockWidth slots V
      0 < g ∧ slots ≤ V*g ∧ g ≤ literal α n ∧ g ≤ link (τ/5) (teams α τ K n) n := by
  have hlit := eventually_blockWidth I (1-α/3) (by linarith)
  have hext := eventually_blockWidth I (1-τ/5-2*α) (by linarith)
  have ht := eventually_many_teams hα τ hK 1
  filter_upwards [hlit,hext,ht,eventually_ge_atTop 1] with n h₁ h₂ ht hn
  intro r hr slots hs hslots V g
  have hv : 0 < V := Fintype.card_pos
  have hroom : slots ≤ V*g := (ceilDiv_le_iff_le_mul hv).mp le_rfl
  have hg : 0 < g := by
    by_contra! hz
    rw [Nat.le_zero.mp hz,mul_zero] at hroom
    omega
  have htotal : r*n ≤ V*blockWidth (r*n) V := (ceilDiv_le_iff_le_mul hv).mp le_rfl
  have hmono : g ≤ blockWidth (r*n) V := (ceilDiv_le_iff_le_mul hv).mpr (hslots.trans htotal)
  refine ⟨hg,hroom,hmono.trans (h₁ r hr),?_⟩
  exact hmono.trans ((h₂ r hr).trans (link_lower hn ht (teams_le hK hn hτ fan)))

/-- Exterior field widths from the manuscript's floor division automatically
meet the per-team incidence bound used in the sewn intercell estimate. -/
theorem physical_exterior_le (ξ : ℝ) (R r n : ℕ) :
    r*R*link ξ (R+1) n ≤ exterior ξ r n := by
  simpa only [exterior,Nat.add_sub_cancel,Nat.mul_assoc] using
    Nat.mul_le_mul_left r (exterior_links_le ξ (R+1) n)

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
