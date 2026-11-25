import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card

/-! # Histograms of the factor indices of a tensor power -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators

/-- Counts the positions bearing each pair of a summand index and a basis index. -/
noncomputable def rankProfileHistogram {n r : ℕ} {X : Type*}
    (s : Fin n → Fin r) (x : Fin n → X) (p : Fin r × X) : Fin (n + 1) := by
  classical
  refine ⟨(Finset.univ.filter fun k => (s k, x k) = p).card, Nat.lt_succ_of_le ?_⟩
  simpa using Finset.card_filter_le Finset.univ (fun k => (s k, x k) = p)

/-- The monomial with exponent vector given by the joint histogram. -/
def rankProfileWeight {F X : Type*} [CommMonoid F] [Fintype X] {r n : ℕ}
    (L : Fin r → X → F) (a : Fin r × X → Fin (n + 1)) : F :=
  ∏ p, L p.1 p.2 ^ (a p : ℕ)

/-- Grouping the factors in a tensor-power term by their pair of indices gives its weight. -/
theorem rankProfileWeight_histogram {F X : Type*} [CommMonoid F] [Fintype X] {r n : ℕ}
    (L : Fin r → X → F) (s : Fin n → Fin r) (x : Fin n → X) :
    rankProfileWeight L (rankProfileHistogram s x) = ∏ k, L (s k) (x k) := by
  classical
  simpa only [rankProfileWeight, rankProfileHistogram, Finset.prod_const] using
    Finset.prod_fiberwise' Finset.univ (fun k => (s k, x k)) (fun p => L p.1 p.2)

end SpectralBooks
end LinearAlgebra
end OAI
