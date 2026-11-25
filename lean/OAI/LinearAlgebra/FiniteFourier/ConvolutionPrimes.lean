import OAI.LinearAlgebra.FiniteFourier.ConvolutionAxisCount
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-! # Packing prime axes and jet coefficients

Given enough logarithmic mass of prime widths, choose distinct axes and a jet
length to place a length-`n` input in a box of volume between `8n` and `9n`.
This is the finite selection argument of Lemma `poly:lem:packing-parameters`.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Finset Real
open scoped BigOperators

section

/-- The volume, jet length, and axis count bounds in the packing lemma.
Here `B` can be a real cutoff. -/
structure PrimeJetPacking (P : Finset ℕ) (n e : ℕ) (B : ℝ) where
  axes : Finset ℕ
  axes_subset : axes ⊆ P
  axes_nonempty : axes.Nonempty
  jet : ℕ
  volume_lower : 8 * n ≤ (∏ p ∈ axes, p) * e * jet
  volume_upper : (∏ p ∈ axes, p) * e * jet ≤ 9 * n
  axes_le : (axes.card : ℝ) ≤ B
  jet_lower : B ≤ (jet : ℝ)
  jet_upper : (jet : ℝ) ≤ 8 * B ^ 2 + 1
  product_le : ∏ p ∈ axes, p ≤ n
  count_le : (axes.card : ℝ) ≤ 9 * log n / log (log n)

/-- A maximum-cardinality feasible subset satisfies the same stopping rule as
the longest feasible prefix. Rounding the quotient up fills the volume gap. -/
theorem exists_primeJetPacking (P : Finset ℕ) {n e : ℕ} {B : ℝ}
    (hn : 0 < n) (he : 1 ≤ e)
    (hP : ∀ p ∈ P, p.Prime ∧ 3 ≤ p ∧ (p : ℝ) ≤ B)
    (hmass : 2 * log n < ∑ p ∈ P, log p) (hbudget : (e : ℝ) * B ^ 2 ≤ n) :
    Nonempty (PrimeJetPacking P n e B) := by
  classical
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he₁ : (1 : ℝ) ≤ e := by exact_mod_cast he
  obtain ⟨p₀, hp₀⟩ : P.Nonempty := by
    by_contra! h
    rw [h, sum_empty] at hmass
    linarith [log_nonneg hn₁]
  have hB : 1 ≤ B := by
    have h := hP p₀ hp₀
    have : (3 : ℝ) ≤ p₀ := by exact_mod_cast h.2.1
    linarith only [this, h.2.2]
  let prodR (s : Finset ℕ) : ℝ := ∏ p ∈ s, (p : ℝ)
  have prod_pos' (s : Finset ℕ) (hs : s ⊆ P) : 0 < prodR s :=
    prod_pos fun p hp ↦ by exact_mod_cast (hP p (hs hp)).1.pos
  have hfull : (n : ℝ) ^ 2 < prodR P := by
    apply (log_lt_log_iff (by positivity) (prod_pos' P Subset.rfl)).mp
    rw [log_pow, log_prod (fun p hp ↦ by exact_mod_cast (hP p hp).1.ne_zero)]
    simpa using hmass
  let feasible := P.powerset.filter fun s ↦ (e : ℝ) * B * prodR s ≤ n
  have hsingle : {p₀} ∈ feasible := by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (singleton_subset_iff.mpr hp₀), ?_⟩
    simp only [prodR, prod_singleton]
    calc
      _ ≤ (e : ℝ) * B * B := mul_le_mul_of_nonneg_left (hP p₀ hp₀).2.2 (by positivity)
      _ = (e : ℝ) * B ^ 2 := by ring
      _ ≤ _ := hbudget
  obtain ⟨s, hs, hmax⟩ := feasible.exists_max_image card ⟨_, hsingle⟩
  obtain ⟨hsP, hfit⟩ := mem_filter.mp hs
  have hsub := mem_powerset.mp hsP
  have hne : s.Nonempty := card_pos.mp (by simpa using hmax _ hsingle)
  have heB : 1 ≤ (e : ℝ) * B := one_le_mul_of_one_le_of_one_le he₁ hB
  have hsn : prodR s ≤ n :=
    (le_mul_of_one_le_left (prod_pos' s hsub).le heB).trans hfit
  obtain ⟨q, hqP, hqs⟩ : ∃ q ∈ P, q ∉ s := by
    by_contra! h
    have heq := Subset.antisymm hsub h
    rw [heq] at hsn
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hmiss : (n : ℝ) < e * B * (q * prodR s) := by
    by_contra! h
    have hi : insert q s ∈ feasible := by
      refine mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hqP hsub), ?_⟩
      simpa only [prodR, prod_insert hqs] using h
    have := hmax _ hi
    simp [card_insert_of_notMem hqs] at this
  let scale := (e : ℝ) * prodR s
  have hscale : 0 < scale := mul_pos (by positivity) (prod_pos' s hsub)
  have hleft : scale * B ≤ n := by simpa [scale, mul_assoc, mul_comm, mul_left_comm] using hfit
  have hright : (n : ℝ) < scale * B ^ 2 := calc
    _ < e * B * (q * prodR s) := hmiss
    _ ≤ e * B * (B * prodR s) := by
      gcongr
      exact (hP q hqP).2.2
    _ = _ := by dsimp [scale]; ring
  let r := ⌈8 * (n : ℝ) / scale⌉₊
  have hquot : 0 ≤ 8 * (n : ℝ) / scale := by positivity
  have hrlo : 8 * (n : ℝ) ≤ r * scale :=
    (div_le_iff₀ hscale).mp (Nat.le_ceil _)
  have hrup : (r : ℝ) * scale < 8 * n + scale := by
    have h := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one hquot) hscale
    rwa [add_mul, div_mul_cancel₀ _ hscale.ne', one_mul] at h
  have hsn' : scale ≤ n := (le_mul_of_one_le_right hscale.le hB).trans hleft
  have hscale' : scale = ((∏ p ∈ s, p : ℕ) : ℝ) * (e : ℝ) := by simp [scale, prodR, mul_comm]
  have hprodNat : ∏ p ∈ s, p ≤ n := by
    apply Nat.cast_le (α := ℝ) |>.mp
    simpa only [Nat.cast_prod] using hsn
  have hn₃ : 3 ≤ n := by
    have hB₃ := (hP p₀ hp₀).2
    have h₃ : (3 : ℝ) ≤ p₀ := by exact_mod_cast hB₃.1
    have := le_mul_of_one_le_left (sq_nonneg B) he₁
    exact_mod_cast (show (3 : ℝ) ≤ n by nlinarith only [h₃, hB₃.2, this, hbudget, sq_nonneg (B - 1)])
  refine ⟨⟨s, hsub, hne, r, ?_, ?_, ?_, ?_, ?_, hprodNat,
    axisCount_le_log_div_loglog hn₃ ((factorial_card_le_prod s
      (fun p hp ↦ (hP p (hsub hp)).1.pos)).trans hprodNat)⟩⟩
  · rw [hscale', mul_comm (r : ℝ)] at hrlo
    exact_mod_cast hrlo
  · have hu : (r : ℝ) * scale ≤ 9 * n := by linarith
    rw [hscale', mul_comm (r : ℝ)] at hu
    exact_mod_cast hu
  · have hi : s ⊆ Icc 1 ⌊B⌋₊ := by
      intro p hp
      exact mem_Icc.mpr ⟨(hP p (hsub hp)).1.one_le, Nat.le_floor (hP p (hsub hp)).2.2⟩
    have hc : s.card ≤ ⌊B⌋₊ := by simpa using card_le_card hi
    exact (Nat.cast_le.mpr hc).trans (Nat.floor_le (by linarith))
  · apply le_of_mul_le_mul_right (a := scale) _ hscale
    nlinarith only [hleft, hrlo, hn₁]
  · apply le_of_mul_le_mul_right (a := scale) _ hscale
    nlinarith only [hrup, hright]

end

end FiniteFourier
end LinearAlgebra
end OAI
