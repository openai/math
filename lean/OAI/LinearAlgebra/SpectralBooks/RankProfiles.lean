import OAI.LinearAlgebra.SpectralBooks.Tensor
import OAI.LinearAlgebra.SpectralBooks.RankProfileHistogram

/-!
# Type-count expansion of bounded-rank tensors

In the expansion of a tensor power, the product of the first-site factors depends
only on the histogram of rank summands and first-site letters. Grouping all three
sites by their histograms gives a fixed spanning family over the ground field.
Each member is itself a sum indexed by the words of rank summands.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

section

noncomputable section

variable {F X Y Z : Type*} [Field F] {r n : ℕ}

/-- Joint multiplicities of a rank summand and a letter in a word of length `n`. -/
abbrev RankProfile (r n : ℕ) (X : Type*) := Fin r × X → Fin (n + 1)

/-- One local histogram at each site of a three-tensor. -/
abbrev TripleRankProfile (r n : ℕ) (X Y Z : Type*) :=
  RankProfile r n X × RankProfile r n Y × RankProfile r n Z

/-- An indicator vector for words of a prescribed joint histogram with `s`. -/
def rankProfileIndicator (s : Fin n → Fin r) (a : RankProfile r n X) (x : Fin n → X) : F := by
  classical
  exact if rankProfileHistogram s x = a then 1 else 0

/-- The tensor counting all rank-summand words with the given three site histograms. -/
def rankProfileTensor (a : RankProfile r n X) (b : RankProfile r n Y) (c : RankProfile r n Z) :
    Tensor F (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∑ s : Fin n → Fin r, Tensor.rankOne
    (rankProfileIndicator s a) (rankProfileIndicator s b) (rankProfileIndicator s c) x y z

theorem rankProfileTensor_rankAtMost (a : RankProfile r n X) (b : RankProfile r n Y)
    (c : RankProfile r n Z) : Tensor.RankAtMost (rankProfileTensor (F := F) a b c) (r ^ n) := by
  unfold rankProfileTensor
  simpa only [rankProfileTensor, Fintype.card_pi_const, Fintype.card_fin] using Tensor.rankAtMost_sum_rankOne
    (fun s => rankProfileIndicator (F := F) s a) (fun s => rankProfileIndicator s b)
    (fun s => rankProfileIndicator s c)

variable [Fintype X] [Fintype Y] [Fintype Z]

/-- The expansion of a rank formula as a linear combination of the profile tensors. -/
theorem power_eq_sum_rankProfileTensors (n : ℕ) (L : Fin r → X → F) (M : Fin r → Y → F)
    (N : Fin r → Z → F) :
    Tensor.power (fun x y z => ∑ i, Tensor.rankOne (L i) (M i) (N i) x y z) n =
      ∑ p : TripleRankProfile r n X Y Z,
        (rankProfileWeight L p.1 * rankProfileWeight M p.2.1 * rankProfileWeight N p.2.2) •
          rankProfileTensor p.1 p.2.1 p.2.2 := by
  classical
  funext x y z
  simp only [Tensor.power, Fintype.prod_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    rankProfileTensor, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun (p : TripleRankProfile r n X Y Z) (s : Fin n → Fin r) => _)]
  apply Finset.sum_congr rfl
  intro s _
  let p : TripleRankProfile r n X Y Z :=
    (rankProfileHistogram s x, rankProfileHistogram s y, rankProfileHistogram s z)
  rw [Finset.sum_eq_single p]
  · simp [p, rankProfileWeight_histogram, Tensor.rankOne, rankProfileIndicator,
      Finset.prod_mul_distrib]
  · rintro ⟨a, b, c⟩ _ hne
    by_cases ha : rankProfileHistogram s x = a <;> by_cases hb : rankProfileHistogram s y = b
    · have hc : rankProfileHistogram s z ≠ c := fun hc => hne (by simp [p, ha, hb, hc])
      simp [Tensor.rankOne, rankProfileIndicator, hc]
    all_goals simp [Tensor.rankOne, rankProfileIndicator, *]
  · simp

/-- Powers of all tensors of rank at most `r` lie in the same profile span. -/
theorem power_mem_span_rankProfileTensors {U : Tensor F X Y Z} {r : ℕ}
    (hU : Tensor.RankAtMost U r) (n : ℕ) : Tensor.power U n ∈ Submodule.span F
      (Set.range (fun p : TripleRankProfile r n X Y Z =>
        rankProfileTensor (F := F) p.1 p.2.1 p.2.2)) := by
  classical
  rcases hU with ⟨L, M, N, rfl⟩
  rw [power_eq_sum_rankProfileTensors]
  exact Submodule.sum_mem _ (fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩))

end

end

end SpectralBooks
end LinearAlgebra
end OAI
