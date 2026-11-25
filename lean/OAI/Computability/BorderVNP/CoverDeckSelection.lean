import OAI.Computability.BorderVNP.CoverDeck
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.Ring

/-!
# Choosing deck digits by the exact squared-deviation score

For one finite candidate motion on p. 21, the centered norm is independent
of the subsequent deck translation. Only correlations between the previously
selected arrays and the translated candidate contribute to the varying term.
This module computes the exact conditional expected increment from residue
histograms and proves that a deterministic minimum on each list of children
preserves the parent's bound.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CoverDeck

open Finset

variable {G H J B : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
  [DecidableEq H] [Fintype B]

/-- The increment of the squared deviation when the next pack is moved by
translation `h`. Its mean at a relative bin `b` is uniform in the tile. -/
def increment (prior candidate : B → G → ℚ) (mean : B → ℚ) (h : G) : ℚ :=
  ∑ b, ∑ x,
    ((candidate b (h * x) - mean b)^2 +
      2 * prior b x * (candidate b (h * x) - mean b))

/-- The part of the increment invariant under the deck translation. -/
def offset (prior candidate : B → G → ℚ) (mean : B → ℚ) : ℚ :=
  ∑ b, ∑ x, ((candidate b x - mean b)^2 - 2 * prior b x * mean b)

omit [Fintype H] in
private theorem increment_expand (prior candidate : B → G → ℚ) (mean : B → ℚ) (h : G) :
    increment prior candidate mean h = offset prior candidate mean +
      2 * ∑ b, ∑ x, candidate b (h * x) * prior b x := by
  simp only [increment, offset, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro b _
  have hinv :
      (∑ x, (candidate b (h * x) - mean b)^2) = ∑ x, (candidate b x - mean b)^2 :=
    Equiv.sum_comp (Equiv.mulLeft h) (fun x => (candidate b x - mean b)^2)
  calc
    _ = (∑ x, (candidate b (h * x) - mean b)^2) -
        (∑ x, 2 * prior b x * mean b) +
        ∑ x, 2 * (candidate b (h * x) * prior b x) := by
      rw [← sum_sub_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun _ _ => by ring
    _ = _ := by rw [hinv, ← sum_sub_distrib, ← sum_add_distrib]

/-- The rational score evaluated for a residue, using two histograms for each
relative bin and a common kernel denominator. -/
def conditionalScore (π : G →* H) (prior candidate : B → G → ℚ) (mean : B → ℚ)
    (c : H) : ℚ :=
  offset prior candidate mean + 2 *
    ∑ b, (∑ v, histogram π (candidate b) (c * v) * histogram π (prior b) v) /
      (fiber π 1).card

/-- The computed score is the actual conditional expected increase of the
squared deviation used to choose motions in §6. -/
theorem conditionalScore_eq (π : G →* H) (hπ : Function.Surjective π)
    (prior candidate : B → G → ℚ) (mean : B → ℚ) (c : H) :
    conditionalScore π prior candidate mean c =
      residueMean π (increment prior candidate mean) c := by
  unfold conditionalScore
  simp_rw [← residueMean_correlation π hπ]
  simp_rw [residueMean, histogram, increment_expand]
  rw [sum_add_distrib, sum_const, ← mul_sum, sum_comm]
  have hk : (fiber π c).card ≠ 0 := by
    obtain ⟨x, hx⟩ := hπ c
    exact card_ne_zero.mpr ⟨x, by simp [fiber, hx]⟩
  have hn : ((fiber π c).card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  rw [nsmul_eq_mul, add_div, mul_div_cancel_left₀ _ hn, mul_div_assoc]
  simp only [div_eq_mul_inv, sum_mul]

/-- Choose the first minimum from an ordered list of children. -/
def chooseResidue (score : H → ℚ) (children : List H) : Option H :=
  children.argmin score

/-- The deterministic choice computed from the histograms is a child and its
expected squared-deviation increment is no greater than at the previous level. -/
theorem chooseResidue_le_parent [DecidableEq J] (π : G →* H) (hπ : Function.Surjective π)
    (ρ : H → J) (hρ : Function.Surjective ρ) (prior candidate : B → G → ℚ) (mean : B → ℚ)
    (c : J) (children : List H) (hchildren : ∀ v, v ∈ children ↔ ρ v = c) :
    ∃ v, chooseResidue (conditionalScore π prior candidate mean) children = some v ∧
      ρ v = c ∧ residueMean π (increment prior candidate mean) v ≤
        residueMean (ρ ∘ π) (increment prior candidate mean) c := by
  obtain ⟨w, hw, _, hwle⟩ :=
    exists_minimizing_child (⇑π) hπ ρ hρ (increment prior candidate mean) c
  have hw' : w ∈ children := (hchildren w).2 (mem_filter.mp hw).2
  cases hh : children.argmin (conditionalScore π prior candidate mean) with
  | none =>
    exact False.elim (List.not_mem_nil (List.argmin_eq_none.mp hh ▸ hw'))
  | some v =>
    refine ⟨v, hh, (hchildren v).mp (List.argmin_mem hh), ?_⟩
    have hle := List.le_of_mem_argmin hw' hh
    rw [conditionalScore_eq π hπ, conditionalScore_eq π hπ] at hle
    exact hle.trans hwle

end CoverDeck

end BorderVNP
end Computability
end OAI
