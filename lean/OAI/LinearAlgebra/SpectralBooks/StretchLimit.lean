import OAI.LinearAlgebra.SpectralBooks.PermutationCover
import Mathlib.Tactic

/-! # Passing to the limit in the permutation stretch

The two upper bounds on the selected summand apply to the same word. After
adding the first with weight `λ` to the second, the sum of the prices of the
letters is bounded by length times the highest letter price. This makes the
bound uniform in the choice of word and permits the limit in Lemma `stretch`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Real
open scoped BigOperators Topology

/-- The selected summand estimates of the permutation stretch imply the
ordinary-sum bound for the combined price `λ a + b + c`. Here `bc` is `b+c`,
`N` is the balanced-word count, and `M` counts the covering permutations.
The word length runs through the multiples `R * k` of the alphabet size. -/
theorem permutationStretch_sum_bound {R L : ℕ} (hR : 0 < R) (hL : 0 < L)
    {lam D E aX bcX : ℝ} (hlam : 0 ≤ lam)
    (a bc : Fin L → ℝ) (N M : ℕ → ℕ)
    (hincrement : bcX = aX + E * logb 2 R)
    (hN : Tendsto (fun k : ℕ ↦ logb 2 (N k) / ((R : ℝ) * k)) atTop (𝓝 (logb 2 R)))
    (hM : Tendsto (fun k : ℕ ↦ logb 2 (M k) / ((R : ℝ) * k)) atTop (𝓝 (logb 2 R)))
    (hselect : ∀ k : ℕ, 0 < k → ∃ (w : Fin (R * k) → Fin L) (z : ℝ),
      (R : ℝ) * k * (aX - D * logb 2 R) + (D + E) * logb 2 (N k) ≤
        z + D * ((R : ℝ) * k) * logb 2 L ∧
      z ≤ (∑ j, a (w j)) + E * logb 2 (M k) ∧
      z ≤ (∑ j, bc (w j)) + E * ((R : ℝ) * k) * logb 2 L) :
    ∃ i : Fin L, lam * aX + bcX ≤ lam * a i + bc i + ((lam + 1) * D + E) * logb 2 L := by
  classical
  have : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image (fun l => lam * a l + bc l)
    Finset.univ_nonempty
  refine ⟨i, ?_⟩
  let P := aX - D * logb 2 R
  let bound (k : ℕ) := (lam + 1) *
      (P + (D + E) * (logb 2 (N k) / ((R : ℝ) * k)) - D * logb 2 L) -
      lam * E * (logb 2 (M k) / ((R : ℝ) * k)) - E * logb 2 L
  have hbound : ∀ᶠ k : ℕ in atTop, bound k ≤ lam * a i + bc i := by
    filter_upwards [eventually_gt_atTop 0] with k hk
    obtain ⟨w, z, hlow, ha, hbc⟩ := hselect k hk
    have hlength : 0 < (R : ℝ) * k := by positivity
    have hwords : lam * (∑ j, a (w j)) + (∑ j, bc (w j)) ≤
        ((R : ℝ) * k) * (lam * a i + bc i) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      calc
        _ ≤ ∑ _j : Fin (R * k), (lam * a i + bc i) :=
          Finset.sum_le_sum fun j _ => hi (w j) (Finset.mem_univ _)
        _ = _ := by simp [mul_add]
    change (R : ℝ) * k * P + _ ≤ _ at hlow
    apply (mul_le_mul_iff_right₀ hlength).mp
    dsimp only [bound]
    have hcancel : (logb 2 (N k) / ((R : ℝ) * k)) * ((R : ℝ) * k) = logb 2 (N k) :=
      div_mul_cancel₀ _ hlength.ne'
    linarith only [hwords, hbc, mul_le_mul_of_nonneg_left ha hlam,
      mul_le_mul_of_nonneg_left hlow (show 0 ≤ lam + 1 by positivity),
      congrArg (fun x => lam * E * x) (div_mul_cancel₀ (logb 2 (M k)) hlength.ne'),
      congrArg (fun x => (lam + 1) * (D + E) * x) hcancel]
  have hlim : Tendsto bound atTop (𝓝 ((lam + 1) * (P + (D + E) * logb 2 R - D * logb 2 L) -
      lam * E * logb 2 R - E * logb 2 L)) := by
    dsimp only [bound]
    exact (((((hN.const_mul (D + E)).const_add P).sub_const (D * logb 2 L)).const_mul
      (lam + 1)).sub (hM.const_mul (lam * E))).sub_const _
  have hfinal := le_of_tendsto hlim hbound
  dsimp only [P] at hfinal
  linarith only [hfinal, hincrement]

/-- Apply the stretch limit to the actual balanced words and their coordinate
permutation covers. For every cover it suffices to establish the three finite
price estimates for one common product word. -/
theorem permutationStretch_sum_bound_of_covers {R L : ℕ} (hR : 0 < R) (hL : 0 < L)
    {lam D E aX bcX : ℝ} (hlam : 0 ≤ lam) (a bc : Fin L → ℝ)
    (hincrement : bcX = aX + E * logb 2 R)
    (hselect : ∀ k : ℕ, 0 < k → ∀ P : Finset (Equiv.Perm (Fin (R * k))),
      (∀ i j : BalancedWords R k, ∃ perm ∈ P, j.1 ∘ perm = i.1) →
      ∃ (w : Fin (R * k) → Fin L) (z : ℝ),
        (R : ℝ) * k * (aX - D * logb 2 R) +
            (D + E) * logb 2 (Fintype.card (BalancedWords R k)) ≤
          z + D * ((R : ℝ) * k) * logb 2 L ∧
        z ≤ (∑ j, a (w j)) + E * logb 2 P.card ∧
        z ≤ (∑ j, bc (w j)) + E * ((R : ℝ) * k) * logb 2 L) :
    ∃ i : Fin L, lam * aX + bcX ≤ lam * a i + bc i + ((lam + 1) * D + E) * logb 2 L := by
  obtain ⟨P, hcover, hlimit⟩ := exists_balanced_permutation_covers hR
  exact permutationStretch_sum_bound hR hL hlam a bc
    (fun k => Fintype.card (BalancedWords R k)) (fun k => (P k).card) hincrement
    (tendsto_logb_card_balancedWords_div_length hR) hlimit
    (fun k hk => hselect k hk (P k) (hcover k))

end SpectralBooks
end LinearAlgebra
end OAI
