import OAI.Computability.BorderVNP.CoverDeckSelection

/-! # Comparing the natural dot products with the exact conditional variance score

The old centered array is its nonnegative physical count minus a binwise rational mean.
The omitted mean contributes the same amount for every possible translation. Thus
sorting by unsigned integer dot products orders the actual rational conditional scores.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckScore

open CoverDeck Finset

variable {B G H : Type*} [Fintype B] [Fintype G] [Fintype H] [DecidableEq H] [Group G] [Group H]

/-- The natural numerator formed from raw physical count arrays. -/
def numerator (π : G →* H) (A C : B → G → ℕ) (c : H) : ℕ :=
  ∑ b, ∑ v, histogram π (C b) (c*v) * histogram π (A b) v

omit [Fintype B] [Fintype H] in
private theorem shifted_hist (π : G →* H) (hπ : Function.Surjective π) (f : G → ℕ)
    (s : ℚ) (v : H) : histogram π (fun g => (f g : ℚ) - s) v =
      ((histogram π f v : ℕ) : ℚ) - (fiber π 1).card * s := by
  simp only [histogram, sum_sub_distrib, sum_const, nsmul_eq_mul, Nat.cast_sum]
  rw [fiber_card_eq_kernel π hπ v]

omit [Fintype B] [Fintype H] in
private theorem cast_hist (π : G →* H) (f : G → ℕ) (v : H) :
    histogram π (fun g => (f g : ℚ)) v = ((histogram π f v : ℕ) : ℚ) := by
  simp [histogram]

private theorem dot_shift (π : G →* H) (hπ : Function.Surjective π) (A C : G → ℕ) (s : ℚ) (c : H) :
    (∑ v, histogram π (fun g => (C g : ℚ)) (c*v) * histogram π (fun g => (A g : ℚ) - s) v) =
      ((∑ v, histogram π C (c*v)*histogram π A v : ℕ) : ℚ) -
        (∑ v, ((histogram π C v : ℕ) : ℚ)) * ((fiber π 1).card * s) := by
  simp only [cast_hist, shifted_hist π hπ, mul_sub, sum_sub_distrib, ← sum_mul, Nat.cast_sum, Nat.cast_mul]
  have he : (∑ i, ((histogram π C (c*i) : ℕ) : ℚ)) = ∑ i, ((histogram π C i : ℕ) : ℚ) :=
    Equiv.sum_comp (Equiv.mulLeft c) (fun v => ((histogram π C v : ℕ) : ℚ))
  rw [he]

/-- For a fixed candidate the exact rational score equals a translation-independent
offset plus a positive multiple of the nonnegative integer numerator. -/
theorem score_affine (π : G →* H) (hπ : Function.Surjective π) (A C : B → G → ℕ)
    (base mean : B → ℚ) :
    ∃ K : ℚ, ∀ c, conditionalScore π (fun b g => (A b g : ℚ) - base b)
      (fun b g => (C b g : ℚ)) mean c = K + 2 * (numerator π A C c : ℚ) / (fiber π 1).card := by
  let den : ℚ := (fiber π 1).card
  refine ⟨offset (fun b g => (A b g : ℚ) - base b) (fun b g => (C b g : ℚ)) mean -
    2 * (∑ b, (∑ v, ((histogram π (C b) v : ℕ) : ℚ)) * (den * base b)) / den, ?_⟩
  intro c
  simp only [conditionalScore, dot_shift π hπ, div_eq_mul_inv, ← sum_mul, sum_sub_distrib,
    numerator, Nat.cast_sum, Nat.cast_mul, den]
  ring

/-- The order computed from the unsigned dot products is exactly the order used by
the paper's conditional-expectation rule on centered arrays, ties included. -/
theorem score_le_iff (π : G →* H) (hπ : Function.Surjective π) (A C : B → G → ℕ)
    (base mean : B → ℚ) (c d : H) :
    conditionalScore π (fun b g => (A b g : ℚ) - base b) (fun b g => (C b g : ℚ)) mean c ≤
      conditionalScore π (fun b g => (A b g : ℚ) - base b) (fun b g => (C b g : ℚ)) mean d ↔
      numerator π A C c ≤ numerator π A C d := by
  obtain ⟨K,h⟩ := score_affine π hπ A C base mean
  have hn : 0 < (fiber π 1).card := Finset.card_pos.mpr ⟨1, by simp [fiber]⟩
  rw [h c, h d, add_le_add_iff_left, div_le_div_iff_of_pos_right (show (0:ℚ) < (fiber π 1).card by exact_mod_cast hn),
    mul_le_mul_iff_right₀ (show (0:ℚ) < 2 by norm_num), Nat.cast_le]

/-- The same comparison orders the actual conditional expected squared deviations. -/
theorem expected_le_iff (π : G →* H) (hπ : Function.Surjective π) (A C : B → G → ℕ)
    (base mean : B → ℚ) (c d : H) :
    residueMean π (increment (fun b g => (A b g : ℚ) - base b) (fun b g => (C b g : ℚ)) mean) c ≤
      residueMean π (increment (fun b g => (A b g : ℚ) - base b) (fun b g => (C b g : ℚ)) mean) d ↔
      numerator π A C c ≤ numerator π A C d := by
  rw [← conditionalScore_eq π hπ, ← conditionalScore_eq π hπ]
  exact score_le_iff π hπ A C base mean c d

end PackedDeckScore

end BorderVNP
end Computability
end OAI
