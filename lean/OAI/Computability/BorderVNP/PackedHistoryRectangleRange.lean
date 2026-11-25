import OAI.Computability.BorderVNP.PackedHistoryRectangles
import OAI.Computability.BorderVNP.ShortenPublicWordRange

/-! # Address and level range for every actual epoch rectangle -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Crossing Shortening.PublicCapacity Shortening.PublicPopulation Cover Packing TeamScales Filter
open scoped Classical

/-- At a physical cover of depth z the true level and the sort addresses fit the
same logarithmic bound at both ends of each epoch. The fixed offset accounts
for a bounded number of extra congruence levels in a relative motion table. -/
theorem boundary_width (I : Type*) [Fintype I] [Nonempty I] {r n z d w : ℕ}
    (s : Shape) (extra factor : ℕ) (hr : 1≤r) (hn : 1≤n)
    (hvol : s.volume (Fintype.card (I → Deck z)) ≤ r*n) (hd : d ≤ z+extra)
    (hw : w ≤ factor*logWidth r n) :
    d+w+Nat.clog 2 (s.sites+2*s.edges+1)+3 ≤ (factor+extra+7)*logWidth r n := by
  let L := logWidth r n
  have hl : 1≤L := by
    change 1 ≤ logWidth r n
    rw [public_logWidth]
    exact (Nat.clog_mono_right 2 (by nlinarith [Nat.mul_le_mul hn hr] : 2≤2*n*r)).trans' (by decide)
  change s.sites+s.edges+Fintype.card (I → Deck z)+1 ≤ r*n at hvol
  have hsort : Nat.clog 2 (s.sites+2*s.edges+1) ≤ L := by
    rw [show L = Nat.clog 2 (2*n*r) from public_logWidth n r]
    exact Nat.clog_mono_right 2 (by nlinarith only [hvol])
  have htile : Nat.clog 2 (Fintype.card (I → Deck z)) ≤ L := by
    rw [show L = Nat.clog 2 (2*n*r) from public_logWidth n r]
    exact Nat.clog_mono_right 2 (by nlinarith only [hvol])
  have hz := depth_le_clog_tiles I z
  have he := Nat.le_mul_of_pos_right extra hl
  change w ≤ factor*L at hw
  change _ ≤ (factor+extra+7)*L
  rw [Nat.add_mul,Nat.add_mul]
  omega

/-- The true maximal rectangle volume (including the final rounded boundary)
lies within the processor address range uniformly in r. -/
theorem eventually_rectangle_range {α τ : ℝ} {g : ℕ} (hα : α<1/1000) (hτ : 0≤τ)
    (hg : 1≤g) (hsmall : τ*Real.logb 2 g ≤ α/10) (A : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (r initial : ℕ), (initial:ℝ) ≤ A*(r*(n:ℝ)^(9/10:ℝ)) →
      g^(epochs τ n)*initial ≤ r*n := by
  filter_upwards [eventually_ge_atTop 1,
    ((tendsto_rpow_atTop (by norm_num : 0<(1/20:ℝ))).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop A]
    with n hn hA
  intro r initial hi
  change A ≤ (n:ℝ)^(1/20:ℝ) at hA
  have hn' : 1≤(n:ℝ) := by exact_mod_cast hn
  have h := epoch_growth_le (by exact_mod_cast hg : 1≤(g:ℝ)) hn hτ hsmall
  have hpow := h.trans (Real.rpow_le_rpow_of_exponent_le hn' (show α/10≤1/20 by linarith))
  have hc : ((g:ℝ)^epochs τ n)*(initial:ℝ) ≤ (r:ℝ)*n := by
    calc
      _ ≤ (n:ℝ)^(1/20:ℝ)*(A*(r*(n:ℝ)^(9/10:ℝ))) := mul_le_mul hpow hi (by positivity) (by positivity)
      _ ≤ (n:ℝ)^(1/20:ℝ)*((n:ℝ)^(1/20:ℝ)*(r*(n:ℝ)^(9/10:ℝ))) := by gcongr
      _ = r*((n:ℝ)^(1/20:ℝ)*(n:ℝ)^(1/20:ℝ)*(n:ℝ)^(9/10:ℝ)) := by ring
      _ = _ := by
        rw [← Real.rpow_add (zero_lt_one.trans_le hn'),← Real.rpow_add (zero_lt_one.trans_le hn')]
        norm_num
  exact_mod_cast hc

/-- The original repeated-width grid uses one physical site per cover tile.
The number of children appears in the tree; widening the repeated bottom
channels does not allocate extra grid sites or extra grid cables. -/
theorem eventually_grid_volume (I : Type*) [Fintype I] [Nonempty I] (dirs : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r →
      let V := Fintype.card (I → Deck (CoverScale.initialDepth I r n+1))
      ((gridShape V dirs).volume V : ℝ) ≤ ((dirs:ℝ)+3)*(r*(n:ℝ)^(9/10:ℝ)) := by
  have large := ((tendsto_rpow_atTop (show 0<(9/10:ℝ) by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (CoverScale.sites I 1 : ℝ)
  filter_upwards [large] with n hbase
  intro r hr V
  change (CoverScale.sites I 1 : ℝ) ≤ (n:ℝ)^(9/10:ℝ) at hbase
  have hr' : 1≤(r:ℝ) := by exact_mod_cast hr
  have scale := (CoverScale.initial_sites I (r := r) (n := n)
    (hbase.trans (le_mul_of_one_le_left (by positivity) hr'))).2
  have hV : (V:ℝ) ≤ r*(n:ℝ)^(9/10:ℝ) := by simpa [CoverScale.sites,V,Fintype.card_fun] using scale
  have hn : 1 ≤ V := Fintype.card_pos
  have hshape : ((gridShape V dirs).volume V : ℝ) ≤ ((dirs:ℝ)+3)*V := by exact_mod_cast grid_volume hn dirs
  exact hshape.trans (mul_le_mul_of_nonneg_left hV (by positivity))

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
