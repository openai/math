import OAI.Computability.BorderVNP.PackedSeedResourceRate
import OAI.Computability.BorderVNP.PackedTailCapacity
import OAI.Computability.BorderVNP.DiagonalTallySidecar

/-! # Literal space for the full original private site tape

One string carries the length header, the padded one-copy box body, and one three-word
sidecar record per possible weighted occurrence. The zero-count sidecar still carries
its own header. All bottom copies at the same site share this string.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid

open Cover CoverScale TeamScales Filter Diagonal.ExternalSew

/-- Common one-copy tape width, independent of the verifier and its private routes. -/
noncomputable def seedDescriptionWidth (n r q depth H bodyCap : ℕ) :=
  H + bodyCap + H*(1 + 3*seedSiteCapacity n r q depth)

/-- Every actual sidecar fits the published site tape. -/
theorem sidecar_room {n r q depth : ℕ} (H bodyCap : ℕ) (ps : List TallySidecar.Position)
    (fits : ps.length ≤ seedSiteCapacity n r q depth) :
    H+bodyCap+(TallySidecar.bits H ps).length ≤ seedDescriptionWidth n r q depth H bodyCap := by
  rw [TallySidecar.bits_length]
  unfold seedDescriptionWidth
  gcongr

private theorem seedTape_le (n r q depth H bodyCap A L D : ℕ) (head : H ≤ A*L^D)
    (body : bodyCap ≤ A*(seedChannelWidth n r q depth+1)*L^D) :
    seedDescriptionWidth n r q depth H bodyCap ≤ 9*A*(seedChannelWidth n r q depth+1)*L^D := by
  let C := seedChannelWidth n r q depth
  have cap := (seed_capacity_le n r q depth).2
  change seedSiteCapacity n r q depth ≤ 2*C at cap
  change bodyCap ≤ A*(C+1)*L^D at body
  change H+bodyCap+H*(1+3*seedSiteCapacity n r q depth) ≤ 9*A*(C+1)*L^D
  nlinarith only [head,body,Nat.mul_le_mul_left H (Nat.mul_le_mul_left 3 cap),
    Nat.mul_le_mul_right (6*C) head,Nat.zero_le (A*L^D),Nat.zero_le (A*L^D*C)]

private theorem batch_mono {r n : ℕ} (hn : 1 ≤ n) {v w : ℝ} (small : v ≤ w)
    (rmax : (r:ℝ) ≤ 2^((n:ℝ)^v)) : (r:ℝ) ≤ 2^((n:ℝ)^w) :=
  rmax.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hn) small))

/-- At the actual selected cover level a padded box with a bounded number of word fields
per incident fine factor fits in one processor half-literal. All original bundles'
full strings, including their sidecars, simultaneously fit in the reserved tails.
The same bound supplies the per-site payload used by the expanded record accounting. -/
theorem eventually_seed_tapes {α τ : ℝ} (hα : 0 < α) (hα' : α < 1/1000) (hτ : 0 < τ)
    (hτ' : τ < α/100) (q D : ℕ) [NeZero q] :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop,
      ∀ r : ℕ, 1 ≤ r → (r:ℝ) ≤ 2^((n:ℝ)^ω) → ∀ depth : ℕ, depth+1 = initialDepth (Fin q) r n →
      ∀ H bodyCap K : ℕ, H ≤ A*(logWidth r n)^D →
        bodyCap ≤ A*(seedChannelWidth n r q depth+1)*(logWidth r n)^D →
        let V := GridHosts.tileCount q depth
        let dB := seedDescriptionWidth n r q depth H bodyCap
        (dB:ℝ) ≤ B*(n:ℝ)^(1/10+τ/20)*(logWidth r n:ℝ)^(D+3) ∧
        ((V*dB : ℕ):ℝ) ≤ B*volume τ r n*(logWidth r n:ℝ)^(D+3) ∧
        dB ≤ literal α n/2 ∧ K^epochs τ n * V * dB ≤ teams α τ K n*r*(literal α n/2) := by
  obtain ⟨u,hu,seed⟩ := eventually_seed_capacity q hτ
  obtain ⟨v,hv,tails⟩ := eventually_private_directory_fits hα hα' hτ hτ' (D+3)
  obtain ⟨w,hw,poly⟩ := exists_polylog_budget (D+3) (show 0 < τ/2000 by positivity)
  let ω := min (min u v) w
  refine ⟨ω,lt_min (lt_min hu hv) hw,fun A => ?_⟩
  let C : ℝ := (96*(4*q+1)+1:ℝ)*factor (Fin q)
  let B := (9*A:ℝ)*(C+1)
  have hB : 0 ≤ B := by dsimp [B,C]; positivity
  refine ⟨B,hB,?_⟩
  have short := eventually_le_rounded_width
    (show 1/10+τ/20+τ/2000 < 1-α/3 by linarith) (show 0 < 1-α/3 by linarith)
    (show (0:ℝ) < 1/2 by norm_num) B
  filter_upwards [seed,tails B hB,poly,short,eventually_ge_atTop 1,
    eventually_rpow_gap (show (0:ℝ) < 9/10 by norm_num) (sites (Fin q) 1)] with n seedN tailN polyN shortN hn coverN
  intro r hr rmax depth hd H bodyCap K head body V dB
  let L := logWidth r n
  let θ := (1/10+τ/20:ℝ)
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 := zero_lt_one.trans_le hn1
  have hr1 : 1 ≤ (r:ℝ) := by exact_mod_cast hr
  have hLN : 1 ≤ L := by
    rw [show L = Nat.clog 2 (2*n*r) from Shortening.PublicCapacity.public_logWidth ..]
    exact (show 1 = Nat.clog 2 2 by decide).le.trans (Nat.clog_mono_right 2 (by nlinarith))
  have hl : 1 ≤ (L:ℝ) := by exact_mod_cast hLN
  have hθ : 1 ≤ (n:ℝ)^θ := Real.one_le_rpow hn1 (by dsimp [θ]; positivity)
  have hc := (seedN r hr (batch_mono hn ((min_le_left _ _).trans (min_le_left _ _)) rmax) depth hd).1
  have hc1 : (seedChannelWidth n r q depth:ℝ)+1 ≤ (C+1)*(n:ℝ)^θ*L^3 := by
    have one := one_le_mul_of_one_le_of_one_le hθ (one_le_pow₀ hl (n:=3))
    change (seedChannelWidth n r q depth:ℝ) ≤ C*(n:ℝ)^θ*L^3 at hc
    linarith
  have raw := seedTape_le n r q depth H bodyCap A L D head body
  have sized : (dB:ℝ) ≤ B*(n:ℝ)^θ*L^(D+3) := calc
    _ ≤ (9*A:ℝ)*((seedChannelWidth n r q depth:ℝ)+1)*L^D := by exact_mod_cast raw
    _ ≤ (9*A:ℝ)*((C+1)*(n:ℝ)^θ*L^3)*L^D := by gcongr
    _ = _ := by rw [pow_add]; dsimp [B]; ring
  have cover : (sites (Fin q) 1:ℝ) ≤ r*(n:ℝ)^(9/10:ℝ) :=
    (by simpa only [Real.rpow_zero,mul_one] using coverN : (sites (Fin q) 1:ℝ) ≤ (n:ℝ)^(9/10:ℝ)).trans
      (le_mul_of_one_le_left (by positivity) hr1)
  have hV := (initial_sites (Fin q) cover).2
  rw [←hd] at hV
  have siteEq : sites (Fin q) (depth+1) = V := by
    dsimp only [V,sites,GridHosts.tileCount]
    simp only [← Nat.card_eq_fintype_card]
  rw [siteEq] at hV
  have total : ((V*dB:ℕ):ℝ) ≤ B*volume τ r n*(L:ℝ)^(D+3) := calc
    _ ≤ (r*(n:ℝ)^(9/10:ℝ))*(B*(n:ℝ)^θ*L^(D+3)) := by push_cast; gcongr
    _ = _ := by
      rw [volume, show (1+τ/20:ℝ) = 9/10+θ by dsimp [θ]; ring,Real.rpow_add hn0 (9/10) θ]; ring
  have small := polyN r hr (batch_mono hn (min_le_right _ _) rmax)
  have smallTape : (dB:ℝ) ≤ (1/2:ℝ)*literal α n := calc
    _ ≤ B*(n:ℝ)^θ*(n:ℝ)^(τ/2000) := sized.trans (mul_le_mul_of_nonneg_left small (by positivity))
    _ = B*(n:ℝ)^(θ+τ/2000) := by rw [Real.rpow_add hn0 θ (τ/2000)]; ring
    _ ≤ _ := shortN
  have fit : dB ≤ literal α n/2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
    exact_mod_cast (show (dB:ℝ)*2 ≤ literal α n by linarith)
  exact ⟨sized,total,fit,tailN r K V dB hr (batch_mono hn ((min_le_left _ _).trans (min_le_right _ _)) rmax) total⟩

end Packing.DeckGrid

end BorderVNP
end Computability
end OAI
