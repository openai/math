import OAI.LinearAlgebra.SpectralBooks.Increment
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! # Passing from finite diagonal labels to the one-site increment inequality -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- The finite diagonal comparison for labels of size `q` implies the one-site
increment bound. Here `a, az, i, iz` are the prices of `A, A ∪ {z}, I, I ∪ {z}`
respectively. Restricting to `q = 2^n` bounds the logarithmic overhead independently of `n`. -/
theorem priceIncrement_of_finite_diagonal {r : ℕ} (hr : 0 < r) {a az i iz : ℝ}
    (hiz : 0 ≤ iz)
    (hfinite : ∀ q : ℕ, 2 ≤ q →
      (az + i) * Real.logb 2 q ≤ a * Real.logb 2 q +
        iz * Real.logb 2 (2 * r * (q - 1) + 1 : ℕ)) :
    az - a ≤ iz - i := by
  by_contra! h
  have hgap : 0 < az + i - a - iz := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt ((iz * Real.logb 2 (2 * r : ℕ)) / (az + i - a - iz))
  let n := m + 1
  let q := 2 ^ n
  have hq : 2 ≤ q := by
    dsimp [q, n]
    rw [pow_succ]
    have : 0 < (2 : ℕ) ^ m := by positivity
    omega
  have hlogq : Real.logb 2 q = n := by
    simp [q, Nat.cast_pow, Real.logb_pow]
  have hsize : 2 * r * (q - 1) + 1 ≤ 2 * r * q := by
    have heq : q = (q - 1) + 1 := by omega
    conv_rhs => rw [heq, Nat.mul_add, Nat.mul_one]
    omega
  have hlogL : Real.logb 2 (2 * r * (q - 1) + 1 : ℕ) ≤
      Real.logb 2 (2 * r : ℕ) + n := by
    rw [← hlogq, ← Real.logb_mul (by positivity) (by positivity)]
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    exact_mod_cast hsize
  have hcomp := (hfinite q hq).trans (add_le_add_right (mul_le_mul_of_nonneg_left hlogL hiz) _)
  rw [hlogq] at hcomp
  have hlarge : iz * Real.logb 2 (2 * r : ℕ) < n * (az + i - a - iz) := by
    exact (div_lt_iff₀ hgap).mp (hm.trans_le (by exact_mod_cast Nat.le_succ m))
  linarith

/-- Intersecting submodularity follows from the finite diagonal comparison on
overlaps of at least two sites, and the single wire bound on one-site overlaps.
The two cases are those in the proof of Lemma `lem:submod`. -/
theorem intersectingSubmodular_of_finite_diagonal {α : Type*} [DecidableEq α]
    (δ : Finset α → ℝ)
    (hnonneg : ∀ S : Finset α, S.Nonempty → 0 ≤ δ S)
    (hsingle : ∀ x : α, δ {x} = 0)
    (hwire : ∀ (A : Finset α) (x z : α), x ∈ A → z ∉ A →
      δ (insert z A) ≤ δ A + δ {x, z})
    (hfinite : ∀ (I A : Finset α) (z : α), 2 ≤ I.card → I ⊆ A → z ∉ A →
      ∀ q : ℕ, 2 ≤ q →
        (δ (insert z A) + δ I) * Real.logb 2 q ≤ δ A * Real.logb 2 q +
          δ (insert z I) * Real.logb 2 (2 * I.card * (q - 1) + 1 : ℕ)) :
    IntersectingSubmodular δ := by
  apply intersectingSubmodular_iff_diminishingIncrements.mpr
  intro I A z hI hIA hz
  have hcard := Finset.card_pos.mpr hI
  by_cases htwo : 2 ≤ I.card
  · exact priceIncrement_of_finite_diagonal hcard (hnonneg _ (Finset.insert_nonempty _ _))
      (hfinite I A z htwo hIA hz)
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (show I.card = 1 by omega)
    have hw := hwire A x z (hIA (Finset.mem_singleton_self x)) hz
    rw [hsingle, sub_zero, Finset.pair_comm z x]
    linarith

end SpectralBooks
end LinearAlgebra
end OAI
