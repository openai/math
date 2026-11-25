import OAI.LinearAlgebra.SpectralBooks.PowerClosure
import OAI.LinearAlgebra.SpectralBooks.RankGrowth
import OAI.LinearAlgebra.SpectralBooks.RankProfiles
import OAI.LinearAlgebra.SpectralBooks.RankSpan
import OAI.LinearAlgebra.SpectralBooks.SpanDescent

/-! # Asymptotic rank is bounded by geometric border rank over every field

For a fixed rank bound, tensor powers of the rank locus lie in the span of a
polynomial number of histogram tensors. Each histogram tensor is defined
over the ground field. A polynomial vanishing argument extends power-span
membership to the closure, and linear descent gives the same expansion over
the ground field. The polynomial factor disappears when taking power roots.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation

variable {F X Y Z : Type*} [Field F]

private theorem scalarExtension_rankProfileTensor {n r : ℕ}
    (a : RankProfile r n X) (b : RankProfile r n Y) (c : RankProfile r n Z) :
    toAlgebraicClosure (rankProfileTensor (F := F) a b c) =
      rankProfileTensor (F := AlgebraicClosure F) a b c := by
  classical
  funext x y z
  simp [toAlgebraicClosure, rankProfileTensor, Tensor.rankOne, rankProfileIndicator,
    apply_ite (algebraMap F (AlgebraicClosure F))]

private theorem scalarExtension_power (T : Tensor F X Y Z) (n : ℕ) :
    toAlgebraicClosure (Tensor.power T n) = Tensor.power (toAlgebraicClosure T) n := by
  funext x y z
  simp [toAlgebraicClosure, Tensor.power]

variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Uniform rank bound for powers of a tensor in the geometric rank-`r` closure. -/
theorem tensorRank_power_le_of_geometricBorderRankAtMost {T : Tensor F X Y Z} {r : ℕ}
    (hT : GeometricBorderRankAtMost T r) (n : ℕ) :
    tensorRank (Tensor.power T n) ≤
      (n + 1) ^ (r * Fintype.card X + r * Fintype.card Y + r * Fintype.card Z) * r ^ n := by
  classical
  let W := fun p : TripleRankProfile r n X Y Z => rankProfileTensor (F := F) p.1 p.2.1 p.2.2
  have hW : Tensor.power T n ∈ Submodule.span F (Set.range W) := by
    apply mem_span_of_toAlgebraicClosure_mem_span
    simp only [W, scalarExtension_power, scalarExtension_rankProfileTensor]
    exact power_mem_span_of_closure hT _ (fun _ hS => power_mem_span_rankProfileTensors hS n)
  have hbound := tensorRank_le_of_rankAtMost (rankAtMost_of_mem_span W
    (fun p => rankProfileTensor_rankAtMost p.1 p.2.1 p.2.2) hW)
  simpa only [TripleRankProfile, RankProfile, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, pow_add, Nat.mul_assoc] using hbound

/-- The middle inequality of the paper's rank comparison, including finite ground fields. -/
theorem asymptoticRank_le_geometricBorderRank (T : Tensor F X Y Z) :
    asymptoticRank T ≤ geometricBorderRank T :=
  asymptoticRank_le_of_polynomial_power_bound T (geometricBorderRank T) _
    (tensorRank_power_le_of_geometricBorderRankAtMost (geometricBorderRankAtMost_geometricBorderRank T))

end SpectralBooks
end LinearAlgebra
end OAI
