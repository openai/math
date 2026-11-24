import OAI.Computability.VPVNP.RAMClock
import OAI.Computability.VPVNP.RAMSiteInput
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Processor strings and counters at large lengths

The logarithmic address and quartic word width can be fixed before selecting
a successful circuit length. The shared messages fit in the processor input
under the live bucket's strictly sublinear growth. The same word width holds
every counter bounded by a fixed polynomial in the input length.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

open Filter RAMLayout

theorem polynomial_lt_wordModulus {n r a : ℕ} (hn : 0 < n) (hr : n.log2 ≤ r) (ha : a ≤ r+1) :
    n^a < 2^((r+10)^4) := by
  have h := (Nat.log2_lt hn.ne').mp (Nat.lt_succ_self n.log2)
  have he : (n.log2+1)*a < (r+10)^4 := by
    have hle := Nat.mul_le_mul (Nat.succ_le_succ hr) ha
    have hsq : (r+1)^2 < (r+10)^2 := Nat.pow_lt_pow_left (by omega) (by decide)
    have hsq' : (r+1)*(r+1) < (r+10)^2 := by simpa only [pow_two] using hsq
    exact lt_of_le_of_lt hle (hsq'.trans_le
      (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 4)))
  exact (Nat.pow_le_pow_left h.le a).trans_lt (by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by decide) he)

/-- Any fixed power eventually fits a word, uniformly in all address
widths at least `log₂ n`. -/
theorem eventually_polynomial_lt_wordModulus (a : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ r, n.log2 ≤ r → n^a < 2^((r+10)^4) := by
  filter_upwards [eventually_ge_atTop (2^a)] with n hn
  have hn0 : 0 < n := (Nat.two_pow_pos _).trans_le hn
  intro r hr
  apply polynomial_lt_wordModulus hn0 hr
  have := (Nat.le_log2 hn0.ne').mpr hn
  omega

/-- Any fixed log-polynomial factor fits inside an arbitrarily small
positive power. This handles the overhead from words, stages and field tags. -/
theorem eventually_polylog_le_rpow (A k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ((A * (n.log2+1)^k : ℕ) : ℝ) ≤ (n : ℝ)^δ := by
  obtain ⟨m, hm⟩ := exists_nat_gt δ⁻¹
  have hm' : 0 < (m : ℝ) := lt_trans (inv_pos.mpr hδ) hm
  have hmd : 1 < δ * m := by
    have := mul_lt_mul_of_pos_left hm hδ
    rwa [mul_inv_cancel₀ hδ.ne'] at this
  filter_upwards [eventually_polylog_le (A^m) (k*m), eventually_ge_atTop 1] with n hp hn
  have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ ((A * (n.log2 + 1)^k : ℕ) : ℝ)^m)
    (show ((A * (n.log2+1)^k : ℕ) : ℝ)^m ≤ n from by
      exact_mod_cast (show (A * (n.log2+1)^k)^m ≤ n from by simpa [mul_pow, ← pow_mul] using hp))
    (inv_nonneg.mpr hm'.le)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    ((A * (n.log2+1)^k : ℕ) : ℝ) = (((A * (n.log2+1)^k : ℕ) : ℝ)^m)^((m:ℝ)⁻¹) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_inv_cancel₀ hm'.ne', Real.rpow_one]
    _ ≤ _ := h
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn' ((inv_le_iff_one_le_mul₀ hm').mpr
      (by simpa [mul_comm] using hmd.le))

/-- A whole site uses only a fixed log-polynomial overhead per bucket
entry. Here `L` is the program-prefix length. -/
private theorem site_length_bound (L B d H t : ℕ) (ht : 1 ≤ t) (hH : 1 ≤ H) (hd : d ≤ B*t) :
    L + (d+4+width d H ((d+10)^4)) ≤
      (L+B+4 + 16*(B+10)^4 + 40*(B+10)^4*(B+1)^2) * H * t^6 := by
  have hl : 1 ≤ H * t^6 := Nat.mul_pos hH (Nat.pow_pos ht)
  have ht6 : t ≤ H*t^6 :=
    (Nat.le_self_pow (by decide) _).trans (Nat.le_mul_of_pos_left _ hH)
  have hs : d+10 ≤ (B+10)*t := by rw [Nat.add_mul]; omega
  have h1 : d+1 ≤ (B+1)*t := by rw [Nat.add_mul]; omega
  have hw : (d+10)^4 ≤ (B+10)^4 * t^4 := by simpa [mul_pow] using Nat.pow_le_pow_left hs 4
  have h4 : t^4 ≤ H*t^6 := (Nat.pow_le_pow_right ht (by decide : 4 ≤ 6)).trans
    (Nat.le_mul_of_pos_left _ hH)
  have hch : (d+1).choose 2 ≤ (B+1)^2 * t^2 := by
    rw [Nat.choose_two_right, ← mul_pow, pow_two]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul h1 (by omega))
  have hd' := hd.trans (Nat.mul_le_mul_left B ht6)
  have hw' := hw.trans (Nat.mul_le_mul_left _ h4)
  rw [width_eq]
  calc
    _ ≤ L*(H*t^6) + (B*(H*t^6)+4*(H*t^6) +
      (16*((B+10)^4*(H*t^6)) + 40*H*((B+10)^4*t^4)*((B+1)^2*t^2))) := by
        gcongr
        · exact Nat.le_mul_of_pos_right _ hl
        · exact Nat.le_mul_of_pos_right _ hl
    _ = _ := by ring

/-- Section 10's live processor layout fits all its fields in `n` input
bits, for any fixed `δ > 0`, prefix, and logarithmic address multiplier. -/
theorem eventually_processorInputFits (p : UniversalMachine.Program) (B : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ d e : ℕ, d ≤ B * (n.log2+1) →
      (2:ℝ)^e ≤ 2*(n:ℝ)^(1-δ) → ProcessorInput.Fits p n d (2^e) ((d+10)^4) := by
  let L := (UniversalMachine.programPrefix p).length
  let K := L+B+4 + 16*(B+10)^4 + 40*(B+10)^4*(B+1)^2
  filter_upwards [eventually_polylog_le_rpow (2*K) 6 hδ, eventually_ge_atTop 1] with n hpoly hn
  intro d e hd hH
  have hlen := site_length_bound L B d (2^e) (n.log2+1) (by omega) (Nat.two_pow_pos e) hd
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have htotal : ((K * 2^e * (n.log2+1)^6 : ℕ) : ℝ) ≤ n := by
    push_cast
    calc
      _ ≤ (K : ℝ)*(2*n^(1-δ))*(n.log2+1)^6 := by gcongr
      _ = (((2*K)*(n.log2+1)^6 : ℕ) : ℝ) * (n:ℝ)^(1-δ) := by push_cast; ring
      _ ≤ n^δ * (n:ℝ)^(1-δ) := mul_le_mul_of_nonneg_right hpoly (by positivity)
      _ = n := by rw [← Real.rpow_add hn', add_sub_cancel, Real.rpow_one]
  exact hlen.trans (by exact_mod_cast htotal)

end BurstRAM

end VPVNP
end Computability
end OAI
