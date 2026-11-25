import Mathlib.Tactic

/-! # From block rank deficits to a lower bound on the sum of list values

This is the counting step in Section 3. The hypotheses refer to the number
of dimensions lost in each block and the spectral value after projection.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier
open scoped BigOperators

theorem projected_list_sum {ι : Type*} [Fintype ι] {n ε : ℝ}
    (hn : 0 < n) (he : 0 < ε) (loss val : ι → ℝ)
    (hloss : ∀ i, 0 ≤ loss i) (hval : ∀ i, 0 ≤ val i)
    (budget : ∑ i, loss i ≤ ε * ((Fintype.card ι : ℝ) * n) / 200)
    (detect : ∀ i, loss i ≤ ε*n → (9/5 : ℝ)*n ≤ val i) :
    (1791/1000 : ℝ) * (Fintype.card ι * n) ≤ ∑ i, val i := by
  classical
  let bad := Finset.univ.filter (fun i => ε*n < loss i)
  let good := Finset.univ \ bad
  have hbad : (bad.card : ℝ) * (ε*n) ≤ ∑ i, loss i := by
    calc
      _ = ∑ _i ∈ bad, ε*n := by simp
      _ ≤ ∑ i ∈ bad, loss i := Finset.sum_le_sum fun i hi =>
        (Finset.mem_filter.mp hi).2.le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hloss i)
  have hfrac : (bad.card : ℝ) ≤ Fintype.card ι / 200 := by
    apply (le_of_mul_le_mul_right _ (mul_pos he hn))
    calc
      _ ≤ _ := hbad.trans budget
      _ = _ := by ring
  have hcards : (good.card : ℝ) + bad.card = Fintype.card ι := by
    exact_mod_cast (by simpa [good] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ bad) :
      good.card + bad.card = Fintype.card ι)
  have hmany : (199/200 : ℝ) * Fintype.card ι ≤ good.card := by linarith
  calc
    _ = ((199/200 : ℝ) * Fintype.card ι) * (9/5*n) := by ring
    _ ≤ (good.card : ℝ) * (9/5*n) := by gcongr
    _ = ∑ _i ∈ good, (9/5*n) := by simp
    _ ≤ ∑ i ∈ good, val i := by
      apply Finset.sum_le_sum
      intro i hi
      apply detect
      have h := (Finset.mem_sdiff.mp hi).2
      simpa [bad] using h
    _ ≤ ∑ i, val i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hval i)

/-- A dictionary estimate of at most `1.79` times total dimension contradicts
the projected-list estimate as soon as the batch and block size are positive. -/
theorem projected_list_obstruction {ι : Type*} [Fintype ι] [Nonempty ι] {n ε : ℝ}
    (hn : 0 < n) (he : 0 < ε) (loss val : ι → ℝ)
    (hloss : ∀ i, 0 ≤ loss i) (hval : ∀ i, 0 ≤ val i)
    (budget : ∑ i, loss i ≤ ε * ((Fintype.card ι : ℝ) * n) / 200)
    (detect : ∀ i, loss i ≤ ε*n → (9/5 : ℝ)*n ≤ val i)
    (dictionary : ∑ i, val i ≤ (179/100 : ℝ) * (Fintype.card ι * n)) : False := by
  have h := (projected_list_sum hn he loss val hloss hval budget detect).trans dictionary
  have hp : 0 < (Fintype.card ι : ℝ) * n := mul_pos (by exact_mod_cast Fintype.card_pos) hn
  linarith

end FiniteFourier
end LinearAlgebra
end OAI
