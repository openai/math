import OAI.Computability.BorderVNP.PackedGridWitnessBudget
import OAI.Computability.BorderVNP.PackedGridWidthBudget
import OAI.Computability.BorderVNP.DiagonalExternalGridBlockHosts

/-!
# Actual one-copy resource scales for a private verifier grid

The common congestion width covers each input interval and bounds the fine
site capacity. On the rounded initial cover, its magnitude is the per-site
verifier volume times the cubic word-length routing cost.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid

open Cover GridPlacement CoverScale TeamScales Filter Diagonal.ExternalSew
open scoped Classical

/-- The width installed on every directed neighbor channel of the wired grid. -/
noncomputable def seedChannelWidth (n r q depth : ℕ) :=
  cableWidth (Fin q → Deck (depth+2)) (endpointBudget (r*n) (batchVolume n r) (GridHosts.tileCount q depth))
    (q*(1+3*depth^3))

/-- Both fine-site occupancy terms and the true grouped input width fit in
the actual common channel budget. -/
theorem seed_capacity_le (n r q depth : ℕ) :
    GridHosts.inputBlockWidth r n q depth ≤ seedChannelWidth n r q depth ∧
    seedSiteCapacity n r q depth ≤ 2*seedChannelWidth n r q depth := by
  let V := GridHosts.tileCount q depth
  let g := blockWidth (r*n) V
  let s := blockWidth (batchVolume n r) V
  let h := q*(1+3*depth^3)
  have hs : g+s ≤ 8*(3*(g+s))*(h+1) := by nlinarith
  change g ≤ 8*(3*(g+s))*(h+1)+Nat.clog 2 V ∧
    g+s+(8*(3*(g+s))*(h+1)+Nat.clog 2 V) ≤ 2*(8*(3*(g+s))*(h+1)+Nat.clog 2 V)
  omega

/-- The explicit ParseBatch verifier volume obeys the paper's input budget
uniformly over processor counts in the stated subexponential range. -/
theorem eventually_batch_volume {τ : ℝ} (ht : 0 < τ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2^((n : ℝ)^ω) →
      (batchVolume n r : ℝ) ≤ volume τ r n := by
  obtain ⟨ω,hω,hpoly⟩ := exists_polylog_budget 3 (show 0 < τ/40 by positivity)
  refine ⟨ω,hω,?_⟩
  filter_upwards [hpoly,eventually_rpow_gap (show τ/40 < τ/20 by linarith) (180000000*64),
    eventually_ge_atTop 1] with n hp hc hn
  intro r hr hmax
  let L := logWidth r n
  have hlen : L = Nat.clog 2 (2*n*r) := Shortening.PublicCapacity.public_logWidth n r
  have hL : 1 ≤ L := hlen ▸ ((by decide : 1 ≤ Nat.clog 2 2).trans (Nat.clog_mono_right 2 (by nlinarith : 2 ≤ 2*n*r)))
  have hlog : Nat.clog 2 (2*n*r)+3 ≤ 4*L := by omega
  have hcube : (((Nat.clog 2 (2*n*r)+3)^3 : ℕ) : ℝ) ≤ 64*(L:ℝ)^3 := by
    have h := Nat.pow_le_pow_left hlog 3
    rw [mul_pow] at h
    exact_mod_cast h
  have hterm : 180000000*((Nat.clog 2 (2*n*r)+3)^3 : ℕ) ≤ (n:ℝ)^(τ/20) := by
    calc
      _ ≤ (180000000*64:ℝ)*(L:ℝ)^3 := by linarith
      _ ≤ _ := (mul_le_mul_of_nonneg_left (hp r hr hmax) (by positivity)).trans hc
  unfold batchVolume volume
  push_cast
  have hn' : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  rw [Real.rpow_add hn',Real.rpow_one]
  convert! mul_le_mul_of_nonneg_left hterm (show 0 ≤ (r:ℝ)*n by positivity) using 1 <;> push_cast <;> ring

private theorem site_count (q depth : ℕ) : sites (Fin q) (depth+1) = GridHosts.tileCount q depth := by
  unfold sites GridHosts.tileCount
  simp only [← Nat.card_eq_fintype_card]

set_option maxHeartbeats 1500000 in
/-- The actual fixed channel width on the chosen initial cover. The level and
both rounding operations are preserved. The constant is uniform in n and r. -/
theorem seedChannelWidth_le {q n r depth : ℕ} [NeZero q] {τ : ℝ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (ht : 0 ≤ τ)
    (small : (GridHosts.tileCount q depth : ℝ) ≤ r*(n : ℝ)^(9/10:ℝ))
    (large : (r : ℝ)*(n : ℝ)^(9/10:ℝ)/factor (Fin q) < GridHosts.tileCount q depth)
    (volumeBound : (batchVolume n r : ℝ) ≤ volume τ r n) :
    (seedChannelWidth n r q depth : ℝ) ≤
      ((96*(4*q+1)+1 : ℝ)*factor (Fin q)) * (n:ℝ)^(1/10+τ/20) * (logWidth r n : ℝ)^3 := by
  let V := GridHosts.tileCount q depth
  let H := seedChannelWidth n r q depth
  let L := (logWidth r n : ℝ)
  let A := (96*(4*q+1)+1 : ℝ)
  let B := (factor (Fin q) : ℝ)
  have hV : (sites (Fin q) (depth+1) : ℝ) ≤ r*(n:ℝ)^(9/10:ℝ) := by rw [site_count]; exact small
  have hraw := grid_width_budget (Fin q) (q := q) (d := depth) hn hr ht hV volumeBound
  dsimp only at hraw
  rw [site_count] at hraw
  have hraw' : (V:ℝ)*H ≤ A*volume τ r n*L^3 := by
    simpa only [V,H,A,L,seedChannelWidth,GridPlacement.cableWidth,← Nat.card_eq_fintype_card] using hraw
  have hB : 0 < B := by
    change 0 < (factor (Fin q) : ℝ)
    exact_mod_cast (Nat.zero_lt_of_lt (one_lt_factor (Fin q)))
  have hv : (r:ℝ)*(n:ℝ)^(9/10:ℝ) ≤ V*B := (div_lt_iff₀ hB).mp large |>.le
  have hn' : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hr' : 0 < (r:ℝ) := by exact_mod_cast (show 0<r by omega)
  have hp : 0 < (r:ℝ)*(n:ℝ)^(9/10:ℝ) := mul_pos hr' (Real.rpow_pos_of_pos hn' _)
  apply (le_of_mul_le_mul_left _ hp)
  calc
    (r:ℝ)*(n:ℝ)^(9/10:ℝ)*H ≤ (V*B)*H := mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg _)
    _ = B*((V:ℝ)*H) := by ring
    _ ≤ B*(A*volume τ r n*L^3) := mul_le_mul_of_nonneg_left hraw' hB.le
    _ = (r:ℝ)*(n:ℝ)^(9/10:ℝ)*(A*B*(n:ℝ)^(1/10+τ/20)*L^3) := by
      rw [volume,show (1:ℝ)+τ/20 = 9/10+(1/10+τ/20) by ring,Real.rpow_add hn']; ring

/-- Eventual one-copy capacities for the level actually selected from the
initial scale, with no choices depending on the private witness. -/
theorem eventually_seed_capacity (q : ℕ) [NeZero q] {τ : ℝ} (ht : 0 < τ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2^((n : ℝ)^ω) →
      ∀ depth : ℕ, depth+1 = initialDepth (Fin q) r n →
      (seedChannelWidth n r q depth : ℝ) ≤
        ((96*(4*q+1)+1:ℝ)*factor (Fin q))*(n:ℝ)^(1/10+τ/20)*(logWidth r n : ℝ)^3 ∧
      GridHosts.inputBlockWidth r n q depth ≤ seedChannelWidth n r q depth ∧
      seedSiteCapacity n r q depth ≤ 2*seedChannelWidth n r q depth := by
  obtain ⟨ω,hω,hbatch⟩ := eventually_batch_volume ht
  refine ⟨ω,hω,?_⟩
  filter_upwards [hbatch,eventually_rpow_gap (show (0:ℝ)<9/10 by norm_num) (sites (Fin q) 1),
    eventually_ge_atTop 1] with n hB hcover hn
  intro r hr hmax depth hd
  have hR : 1 ≤ (r:ℝ) := by exact_mod_cast hr
  have hcover' : (sites (Fin q) 1 : ℝ) ≤ r*(n:ℝ)^(9/10:ℝ) :=
    (by simpa only [Real.rpow_zero,mul_one] using hcover : (sites (Fin q) 1 : ℝ) ≤ (n:ℝ)^(9/10:ℝ)).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) hR)
  have h := initial_sites (Fin q) hcover'
  rw [← hd,site_count] at h
  exact ⟨seedChannelWidth_le hn hr ht.le h.2 h.1 (hB r hr hmax),seed_capacity_le ..⟩

end Packing.DeckGrid

end BorderVNP
end Computability
end OAI
