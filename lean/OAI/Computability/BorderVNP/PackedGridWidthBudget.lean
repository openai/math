import OAI.Computability.BorderVNP.PackedGridSlots
import OAI.Computability.BorderVNP.PackedCoverScale
import OAI.Computability.BorderVNP.ShortenPublicPaddedWords

/-! # Total width of the public neighbor grid

The paper routes one fixed width along every directed channel. Multiplying
the two rounded endpoint capacities by the number of sites recovers the
total leaf and vertex budgets, up to one additional site count each. The
cubic diameter of the deck contributes three binary address logarithms.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridPlacement

open CoverScale TeamScales
open scoped Classical

private theorem block_product_le (n V : ℕ) :
    V * blockWidth n V ≤ n + V := by
  unfold blockWidth
  rw [Nat.ceilDiv_eq_add_pred_div]
  exact (Nat.mul_div_le _ _).trans (by omega)

/-- The depth of a stable product deck with at most the physical slot
budget is bounded by the actual machine address width. -/
theorem depth_le_logWidth (I : Type) [Fintype I] [Nonempty I] {d r n : ℕ}
    (hv : sites I (d+1) ≤ r*n) : d ≤ logWidth r n := by
  have hpow : 2^d ≤ sites I (d+1) := by
    rw [sites_stable]
    have hv1 : 0 < sites I 1 := Fintype.card_pos
    exact (Nat.pow_le_pow_left (one_lt_factor I) _).trans (Nat.le_mul_of_pos_right _ hv1)
  rw [Shortening.PublicCapacity.public_logWidth]
  exact (Nat.le_log_of_pow_le (by decide) hpow).trans ((Nat.log_le_clog 2 _).trans
    (Nat.clog_mono_right _ (hv.trans (by nlinarith))))

/-- Every site and uniform Cayley channel, with the rounded block widths and
the actual integral congestion bound used by the public routing. The bound
is independent of the private routing choices and of the team size. -/
theorem grid_width_budget_with_factor (I : Type) [Fintype I] [Nonempty I] {q d r n s : ℕ} {τ C : ℝ} (hC : 1 ≤ C)
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hτ : 0 ≤ τ)
    (hsite : (sites I (d+1) : ℝ) ≤ r * (n : ℝ) ^ (9/10 : ℝ)) (hs : (s : ℝ) ≤ C * volume τ r n) :
    let V := sites I (d+1)
    let H := cableWidth (I → Cover.Deck (d+2)) (endpointBudget (r*n) s V) (q*(1+3*d^3))
    (V : ℝ) * H ≤ (96 * (4*q+1) + 1 : ℝ) * (C * volume τ r n) * (logWidth r n : ℝ)^3 := by
  let V := sites I (d+1)
  let L := logWidth r n
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hL : 1 ≤ L := by
    rw [show L = Nat.clog 2 (2*n*r) from Shortening.PublicCapacity.public_logWidth ..]
    have h := Nat.clog_mono_right 2 (show 2 ≤ 2*n*r by nlinarith)
    exact (show 1 = Nat.clog 2 2 by decide).le.trans h
  have hV : V ≤ r*n := by
    apply (Nat.cast_le (α := ℝ)).mp
    rw [Nat.cast_mul]
    apply hsite.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    simpa using (Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (9/10:ℝ) ≤ 1))
  have hslots : ((r*n : ℕ) : ℝ) ≤ volume τ r n := by
    rw [Nat.cast_mul]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    simpa using (Real.rpow_le_rpow_of_exponent_le hn' (by linarith : 1 ≤ 1+τ/20))
  have hbudget : volume τ r n ≤ C * volume τ r n :=
    le_mul_of_one_le_left ((Nat.cast_nonneg (r*n)).trans hslots) hC
  have hd : d ≤ L := depth_le_logWidth I hV
  have hc : Nat.clog 2 V ≤ L := by
    rw [show L = Nat.clog 2 (2*n*r) from Shortening.PublicCapacity.public_logWidth ..]
    exact Nat.clog_mono_right 2 (hV.trans (by nlinarith))
  have hh : q*(1+3*d^3)+1 ≤ (4*q+1)*L^3 := by
    have hp := Nat.pow_le_pow_left hd 3
    have hp' : 1 ≤ L^3 := Nat.one_le_pow _ _ hL
    nlinarith [Nat.mul_le_mul_left q hp,Nat.mul_le_mul_left q hp']
  have endp : V * endpointBudget (r*n) s V ≤ 3*(r*n+s+2*V) := by
    unfold endpointBudget
    have h1 := block_product_le (r*n) V
    have h2 := block_product_le s V
    nlinarith
  have hlog : L ≤ L^3 := by nlinarith [Nat.one_le_pow 2 L hL,Nat.mul_le_mul_left L (Nat.one_le_pow 2 L hL)]
  have hcount : Fintype.card (I → Cover.Deck (d+2)) = V := by
    unfold V sites
    simp only [← Nat.card_eq_fintype_card]
  let H := cableWidth (I → Cover.Deck (d+2)) (endpointBudget (r*n) s V) (q*(1+3*d^3))
  have hraw : V*H ≤ (24*(r*n+s+2*V)*(4*q+1)+V)*L^3 := by
    unfold H cableWidth
    rw [hcount]
    calc
      _ = 8*(V*endpointBudget (r*n) s V)*(q*(1+3*d^3)+1) + V*Nat.clog 2 V := by ring
      _ ≤ 8*(3*(r*n+s+2*V))*((4*q+1)*L^3) + V*L^3 := by
        gcongr; exact hc.trans hlog
      _ = _ := by ring
  have hv' : (V : ℝ) ≤ volume τ r n := (Nat.cast_le.mpr hV).trans hslots
  have hraw' : (V : ℝ)*H ≤ (24*((r*n : ℕ)+s+2*(V : ℝ))*(4*q+1)+V)*(L : ℝ)^3 := by
    exact_mod_cast hraw
  let B := C * volume τ r n
  have hvB : (V : ℝ) ≤ B := hv'.trans hbudget
  apply hraw'.trans
  calc
    _ ≤ (24*(B+B+2*B)*(4*q+1)+B)*(L : ℝ)^3 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply add_le_add _ hvB
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (add_le_add (hslots.trans hbudget) hs) (mul_le_mul_of_nonneg_left hvB (by norm_num))
    _ = _ := by dsimp only [B]; ring

/-- The unit-volume specialization of the uniform grid bound. -/
theorem grid_width_budget (I : Type) [Fintype I] [Nonempty I] {q d r n s : ℕ} {τ : ℝ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hτ : 0 ≤ τ)
    (hsite : (sites I (d+1) : ℝ) ≤ r * (n : ℝ) ^ (9/10 : ℝ)) (hs : (s : ℝ) ≤ volume τ r n) :
    let V := sites I (d+1)
    let H := cableWidth (I → Cover.Deck (d+2)) (endpointBudget (r*n) s V) (q*(1+3*d^3))
    (V : ℝ) * H ≤ (96 * (4*q+1) + 1 : ℝ) * volume τ r n * (logWidth r n : ℝ)^3 := by
  simpa only [one_mul] using
    (grid_width_budget_with_factor I (q := q) (s := s) (C := 1) le_rfl hn hr hτ hsite (by simpa only [one_mul] using hs))

end Packing.GridPlacement

end BorderVNP
end Computability
end OAI
