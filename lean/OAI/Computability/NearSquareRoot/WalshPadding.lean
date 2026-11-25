import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Log
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith

/-!
# Spectator rows for the selected-bit Walsh transform

Pad the spectator field once to a multiple of `W ^ J`. Every child then gets a whole
number of rows, while each original row still contains all `2 ^ s` selected addresses.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace WalshPadding

open Filter

/-- For `s ≥ 2`, the largest piece uses `2 * A ^ (depth A s)` selected bits. -/
def depth (A s : ℕ) : ℕ := Nat.log A (s / 2)

/-- Pad a row count up to a multiple of the combined fanout of all levels. -/
def paddedRows (q W J : ℕ) : ℕ := W ^ J * (q ⌈/⌉ W ^ J)

theorem rows_le_paddedRows {q W J : ℕ} (hW : 0 < W) : q ≤ paddedRows q W J :=
  (ceilDiv_le_iff_le_mul (Nat.pow_pos hW)).mp le_rfl

theorem paddedRows_lt {q W J : ℕ} (hW : 0 < W) : paddedRows q W J < q + W ^ J := by
  have hp : 0 < W ^ J := Nat.pow_pos hW
  unfold paddedRows
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.mul_comm]
  exact (Nat.div_mul_le_self _ _).trans_lt (by omega)

theorem paddedRows_le_double {q W J : ℕ} (hW : 0 < W) (hq : W ^ J ≤ q) :
    paddedRows q W J ≤ 2 * q := by
  have := paddedRows_lt (q := q) (J := J) hW
  omega

/-- After `i` splits by residues modulo `W`, the leading count is still a
multiple of the fanout needed for the remaining `J - i` levels. -/
theorem split_divisibility (q W J i : ℕ) (hi : i ≤ J) :
    W ^ (J - i) ∣ paddedRows q W J / W ^ i := by
  apply Nat.dvd_div_of_mul_dvd
  rw [← pow_add, Nat.add_sub_of_le hi]
  exact dvd_mul_right ..

/-- Splitting into residue classes creates equal streams, with exactly the
original number of records across them. `R` is the complete spectator and
selected-address range within a row. -/
theorem split_volume {q W J i : ℕ} (hi : i < J) (R : ℕ) :
    W * ((paddedRows q W J / W ^ i / W) * R) = (paddedRows q W J / W ^ i) * R := by
  rw [← Nat.mul_assoc]
  congr 1
  apply Nat.mul_div_cancel'
  exact (dvd_pow_self W (by omega : J - i ≠ 0)).trans (split_divisibility q W J i hi.le)

/-- Dividing a row number by the batch width gives its index on a child stream,
and the remainder selects the stream. The inverse linear address interleaves
the children in the original order. -/
def splitRows (groups W : ℕ) : Fin (groups * W) ≃ Fin groups × Fin W :=
  finProdFinEquiv.symm

@[simp] theorem splitRows_group {groups W : ℕ} (r : Fin (groups * W)) :
    ((splitRows groups W r).1 : ℕ) = r.val / W := rfl

@[simp] theorem splitRows_stream {groups W : ℕ} (r : Fin (groups * W)) :
    ((splitRows groups W r).2 : ℕ) = r.val % W := rfl

theorem batchModulus_le_poly {A s : ℕ} (hA : 2 ≤ A) (hs : 2 ≤ s) (W : ℕ) :
    W ^ depth A s ≤ (s / 2) ^ W := by
  have hbase := W.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hA W)
  calc
    W ^ depth A s ≤ (A ^ W) ^ depth A s := Nat.pow_le_pow_left hbase _
    _ = (A ^ depth A s) ^ W := by rw [← pow_mul, mul_comm, pow_mul]
    _ ≤ (s / 2) ^ W := Nat.pow_le_pow_left (Nat.pow_log_le_self _ (by omega)) _

/-- The sparse selection condition eventually leaves at least half the address
bits available as spectators, uniformly over every allowed choice of `s`. -/
theorem eventually_twice_selected_le (c : ℝ) (hc : 0 < c) :
    ∀ᶠ k : ℕ in atTop, ∀ s : ℕ,
      (s : ℝ) ≤ c * k / Real.log (2 + k) → 2 * s ≤ k := by
  have htop : Tendsto (fun k : ℕ => Real.log (2 + k)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  filter_upwards [htop.eventually_ge_atTop (2 * c)] with k hk
  intro s hs
  have hpos : 0 < Real.log (2 + k) := lt_of_lt_of_le (by positivity : 0 < 2 * c) hk
  have he := (le_div_iff₀ hpos).mp hs
  have hh : (s : ℝ) * (2 * c) ≤ c * k :=
    (mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg s)).trans he
  have : (2 : ℝ) * s ≤ k := by
    apply le_of_mul_le_mul_right (a := c) _ hc
    linarith only [hh]
  exact_mod_cast this

open Asymptotics in
/-- Fixed polynomial fanout is eventually smaller than the available spectator field. -/
theorem eventually_pow_le_two_pow_half (d : ℕ) :
    ∀ᶠ k : ℕ in atTop, k ^ d ≤ 2 ^ (k / 2) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) (d + 1) (by norm_num : (1 : ℝ) < 2)).def
      zero_lt_one)
  filter_upwards [eventually_ge_atTop (2 * max N (3 ^ d) + 2)] with k hk
  have hj : N ≤ k / 2 := by omega
  have h3 : 3 ^ d ≤ k / 2 := by omega
  have hpoly : (k / 2) ^ (d + 1) ≤ 2 ^ (k / 2) := by
    have hs := hN (k / 2) hj
    simp only [Real.norm_eq_abs, abs_pow, Nat.abs_cast, abs_of_pos (by norm_num : (0:ℝ)<2),
      one_mul] at hs
    exact_mod_cast hs
  calc k ^ d ≤ (3 * (k / 2)) ^ d := Nat.pow_le_pow_left (by omega) _
       _ = (k / 2)^d * 3^d := by rw [mul_pow, mul_comm]
       _ ≤ (k / 2)^d * (k / 2) := Nat.mul_le_mul_left _ h3
       _ = (k / 2)^(d+1) := (pow_succ _ _).symm
       _ ≤ 2 ^ (k / 2) := hpoly

/-- Padding all levels of a Walsh piece simultaneously adds at most one copy
of the original array, uniformly over the selected bits. -/
theorem eventually_paddedRows_bound {A W : ℕ} (hA : 2 ≤ A) (hW : 0 < W)
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ k : ℕ in atTop, ∀ s : ℕ, (s : ℝ) ≤ c * k / Real.log (2 + k) →
      let q := 2 ^ (k - s)
      let q' := paddedRows q W (depth A s)
      W ^ depth A s ≤ q ∧ q ≤ q' ∧ q' ≤ 2 * q ∧
        2 ^ k ≤ q' * 2 ^ s ∧ q' * 2 ^ s ≤ 2 * 2 ^ k := by
  filter_upwards [eventually_twice_selected_le c hc, eventually_pow_le_two_pow_half W]
    with k hhalf hpoly
  intro s hs
  have hsk := hhalf s hs
  have he : W ^ depth A s ≤ 2 ^ (k - s) := by
    by_cases h : 2 ≤ s
    · calc
        W ^ depth A s ≤ (s / 2) ^ W := batchModulus_le_poly hA h W
        _ ≤ k ^ W := Nat.pow_le_pow_left (by omega) _
        _ ≤ 2 ^ (k / 2) := hpoly
        _ ≤ 2 ^ (k - s) := Nat.pow_le_pow_right (by decide) (by omega)
    · simpa [depth, show s / 2 = 0 by omega] using (Nat.one_le_two_pow (n := k - s))
  have hraw : 2 ^ (k - s) * 2 ^ s = 2 ^ k :=
    (pow_add 2 (k - s) s).symm.trans (by rw [Nat.sub_add_cancel (by omega)])
  dsimp only
  refine ⟨he, rows_le_paddedRows hW, paddedRows_le_double hW he, ?_, ?_⟩
  · rw [← hraw]
    exact Nat.mul_le_mul_right _ (rows_le_paddedRows hW)
  · calc
      paddedRows (2 ^ (k - s)) W (depth A s) * 2 ^ s ≤
        (2 * 2 ^ (k - s)) * 2 ^ s := Nat.mul_le_mul_right _ (paddedRows_le_double hW he)
      _ = 2 * 2 ^ k := by rw [Nat.mul_assoc, hraw]

end WalshPadding

end NearSquareRoot
end Computability
end OAI
