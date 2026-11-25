import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic

open scoped BigOperators

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

/-- Distinct subset sums of the proxy logarithms differ by more than two. -/
def IsDissociated {ι : Type*} (l : ι → ℝ) (J : Finset ι) : Prop :=
  ∀ A ⊆ J, ∀ B ⊆ J, A ≠ B → 2 < |(∑ i ∈ A, l i) - ∑ i ∈ B, l i|

theorem IsDissociated.mono {ι : Type*} {l : ι → ℝ} {I J : Finset ι}
    (h : IsDissociated l J) (hIJ : I ⊆ J) : IsDissociated l I :=
  fun A hA B hB hAB ↦ h A (hA.trans hIJ) B (hB.trans hIJ) hAB

end Compression
end LinearProgramming
end Optimization
end OAI
