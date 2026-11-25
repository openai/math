import OAI.LinearAlgebra.SpectralBooks.Fermion.Pascal
import OAI.LinearAlgebra.SpectralBooks.Fermion.Fermion
import Mathlib.LinearAlgebra.Matrix.Block

/-! # The energy filtration of the exterior Pascal matrix -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open Finset Matrix

/-- A principal minor is lower triangular with every diagonal entry equal to one. -/
@[simp] theorem pascalMinor_self (I : Finset ℕ) : pascalMinor I I = 1 := by
  classical
  unfold pascalMinor stateMinor
  rw [dite_eq_left rfl]
  rw [Matrix.det_of_isLowerTriangular]
  · simp
  · intro i j hij
    change i < j at hij
    simp [Nat.choose_eq_zero_of_lt ((I.orderEmbOfFin rfl).strictMono hij)]

private theorem weight_enumeration (S : Finset ℕ) {k : ℕ} (h : S.card = k) :
    weight S = ∑ i : Fin k, (2 * S.orderEmbOfFin h i + 1) := by
  calc
    weight S = ∑ j ∈ univ.map (S.orderEmbOfFin h).toEmbedding, (2*j + 1) := by
      rw [S.map_orderEmbOfFin_univ]
      rfl
    _ = _ := sum_map _ _ _

/-- In any nonzero Pascal minor, either the occupation sets coincide or the
column occupation has strictly smaller energy than the row occupation. -/
theorem eq_or_weight_lt_of_pascalMinor_ne_zero {I J : Finset ℕ} (h : pascalMinor I J ≠ 0) :
    I = J ∨ weight J < weight I := by
  classical
  by_cases hc : J.card = I.card
  · simp only [pascalMinor, stateMinor, dite_eq_left hc, Matrix.det_apply', Matrix.of_apply] at h
    obtain ⟨σ, _, hσ⟩ := exists_ne_zero_of_sum_ne_zero h
    have hle (i : Fin I.card) : J.orderEmbOfFin hc i ≤ I.orderEmbOfFin rfl (σ i) := by
      by_contra! hn
      have hz := prod_eq_zero (s := univ) (mem_univ i)
        (f := fun j : Fin I.card ↦ (((I.orderEmbOfFin rfl (σ j)).choose (J.orderEmbOfFin hc j)) : ℤ))
        (by simp [Nat.choose_eq_zero_of_lt hn])
      exact hσ (by simp [hz])
    by_cases heq : ∀ i, J.orderEmbOfFin hc i = I.orderEmbOfFin rfl (σ i)
    · left
      symm
      apply eq_of_subset_of_card_le _ hc.ge
      intro n hn
      obtain ⟨i, hi⟩ := (J.orderIsoOfFin hc).surjective ⟨n, hn⟩
      have hi' : J.orderEmbOfFin hc i = n := congrArg Subtype.val hi
      rw [← hi', heq]
      exact I.orderEmbOfFin_mem rfl _
    · right
      push Not at heq
      obtain ⟨i, hi⟩ := heq
      rw [weight_enumeration J hc, weight_enumeration I rfl,
        ← Equiv.sum_comp σ (fun j ↦ 2 * I.orderEmbOfFin rfl j + 1)]
      apply sum_lt_sum (fun j _ ↦ by have := hle j; omega)
      exact ⟨i, mem_univ i, by have := hle i; omega⟩
  · simp [pascalMinor, stateMinor, hc] at h

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
