import OAI.LinearAlgebra.SpectralBooks.GaussianTest
import OAI.LinearAlgebra.SpectralBooks.StudentLaw
import OAI.LinearAlgebra.SpectralBooks.StudentThreshold

/-! # From unbounded flat dimensions to the Gaussian rectangular test -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter
open scoped Topology

section

/-- The finite-dimensional sum of Student upper tails in the higher-flat theorem.
The variable `d` counts degrees of freedom. -/
def StudentBound (d : ℕ) (m : Fin 3 → ℝ) (L : ℝ) : Prop :=
  ∑ i ∈ Finset.univ.filter (fun i => 0 < m i),
    studentTail d (Real.sqrt ((d : ℝ) * ((L / m i) ^ (2 / ((d : ℝ) - 1)) - 1))) ≤ 1

/-- If the Student tests hold in arbitrarily large dimensions, the Gaussian
test holds. No common probability space for the different dimensions is required. -/
theorem gaussianBound_of_frequently_studentBound {m : Fin 3 → ℝ} {L : ℝ}
    (hmL : ∀ i, m i ≤ L) (h : ∃ᶠ d : ℕ in atTop, StudentBound d m L) :
    GaussianBound m L := by
  let s := Finset.univ.filter (fun i => 0 < m i)
  have hlim := tendsto_finsetSum s fun i hi =>
    studentTail_tendsto (tendsto_studentThreshold ((Finset.mem_filter.mp hi).2) (hmL i))
  exact le_of_tendsto_of_frequently hlim h

end

end SpectralBooks
end LinearAlgebra
end OAI
