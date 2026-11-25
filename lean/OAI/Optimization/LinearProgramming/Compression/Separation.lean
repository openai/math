import OAI.Optimization.LinearProgramming.Compression.SeparationLogs
import OAI.Optimization.LinearProgramming.Compression.SeparationDominance
import Mathlib.Data.Finset.Powerset

open scoped BigOperators

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

/-- All sums of distinct subproducts are different for a dissociated family of proxy logs. -/
theorem dissociated_subsetProduct_subsetSum_injOn {ι : Type*} [DecidableEq ι]
    {l x : ι → ℝ} {J : Finset ι} (hd : IsDissociated l J)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : (J.card : ℝ) * η ≤ 1)
    (hn : ∀ i ∈ J, x i ≠ 0) (herr : ∀ i ∈ J, |l i - Real.logb 2 (|x i|)| ≤ η) :
    Set.InjOn (fun U : Finset (Finset ι) ↦ ∑ A ∈ U, ∏ i ∈ A, x i)
      (↑J.powerset.powerset : Set (Finset (Finset ι))) := by
  apply subsetSum_injOn_of_doubling J.powerset (fun A ↦ ∏ i ∈ A, x i)
  · exact fun A hA ↦ Finset.prod_ne_zero_iff.mpr fun i hi ↦ hn i (Finset.mem_powerset.mp hA hi)
  · exact fun A hA B hB ↦ hd.subsetProduct_doubling hη hsmall hn herr
      (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB)

end Compression
end LinearProgramming
end Optimization
end OAI
