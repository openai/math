import OAI.LinearAlgebra.SpectralBooks.Fermion.FermionCutoff

/-! # Energy conservation in the truncated crossing identity -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open Finset
open scoped BigOperators

/-- The finite supercommutator entry, including its binomial multiplier. -/
noncomputable def truncatedRhs (i j α β : State) (s : ℤ) (N : ℕ) : ℤ :=
  let L := order (weight i) (weight j)
  ∑ a ∈ range (L+1), multiplier L a *
    ((∑ k ∈ (range N).powerset, blockMode i (-s-1-L+a) α k * blockMode j (s-a) k β) -
      (-1)^(i.card*j.card) * ∑ k ∈ (range N).powerset,
        blockMode j (s-a) α k * blockMode i (-s-1-L+a) k β)

/-- The two field weights determine the multiplier degree exactly. -/
theorem two_mul_order_add {i j : State} (hi : i.Nonempty) (hij : i.card = j.card) :
    2 * (order (weight i) (weight j) : ℤ) + 2 = (weight i : ℤ) + weight j := by
  have hw (S : State) : weight S = 2 * ∑ k ∈ S, k + S.card := by
    simp [weight, sum_add_distrib, mul_sum]
  have hp := card_pos.mpr hi
  simp only [order, hw]
  omega

/-- Each product order preserves total energy after extracting the two modes. -/
theorem truncatedRhs_eq_zero_of_weight_ne {i j α β : State}
    (hi : i.Nonempty) (hij : i.card = j.card) (hαβ : weight α ≠ weight β)
    (s : ℤ) (N : ℕ) : truncatedRhs i j α β s N = 0 := by
  let L := order (weight i) (weight j)
  have hL : 2 * (L : ℤ) + 2 = (weight i : ℤ) + weight j := two_mul_order_add hi hij
  have hz {I J : State} {b c : ℤ} (h : (weight I : ℤ) + weight J + 2*(b+c) = 0) :
      ∑ k ∈ (range N).powerset, blockMode I b α k * blockMode J c k β = 0 := by
    apply sum_eq_zero
    intro k _
    by_contra hne
    obtain ⟨h₁, h₂⟩ := mul_ne_zero_iff.mp hne
    have hα := weight_eq_of_blockMode_ne_zero h₁
    have hβ := weight_eq_of_blockMode_ne_zero h₂
    omega
  unfold truncatedRhs
  dsimp only
  apply sum_eq_zero
  intro a _
  change multiplier L a * _ = 0
  rw [hz (I := i) (J := j) (b := -s-1-L+a) (c := s-a) (by omega),
      hz (I := j) (J := i) (b := s-a) (c := -s-1-L+a) (by omega)]
  simp

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
