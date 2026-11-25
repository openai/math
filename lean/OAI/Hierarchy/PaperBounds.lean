import OAI.Hierarchy.ConditionalGrid
import OAI.Hierarchy.FlatFieldTransfer
import OAI.Hierarchy.Flat

namespace OAI
/-! # The paper's arithmetic separations and square matrix multiplication bound -/

namespace Hierarchy

open Filter LinearAlgebra.SpectralBooks

/-- Cofinality in the prime fields suffices even for the homogeneous price
systems needed for the path, binary tree and grid over arbitrary fields. -/
theorem UnboundedPrimeFieldFlats.all_dimensions (h : UnboundedPrimeFieldFlats)
    (F : Type*) [Field F] (d : ℕ) : HasSpectralFlat F d := by
  apply HasSpectralFlat.of_prime_fields _ F
  intro p _
  obtain ⟨n, flat, large⟩ := ((h p).and_eventually (eventually_ge_atTop d)).exists
  exact HasSpectralFlat.of_le large flat

/-- The graph hypothesis is the homogeneous-flats implication of the published
graph theorem. The common geometric hypothesis only concerns the prime fields. -/
theorem paper_bounds_of_prime_flats (h : UnboundedPrimeFieldFlats) (F : Type*) [Field F]
    (graph : LowDegreeGraphTheorem F) :
    (VF F ⊂ VBP F ∧ VBP F ⊂ VP F ∧ VP F ⊂ VNP F) ∧
    2 * Real.exp (stdNormalQuantile (2 / 3) ^ 2 / 2) ≤ formalOmega F 1 1 1 ∧
    (1097 : ℝ)/500 < formalOmega F 1 1 1 := by
  exact ⟨strict_inclusions_of_graph_classification F graph
    (fun d _ => h.all_dimensions (AlgebraicClosure (⊥ : Subfield F)) d),
    square_exponent_of_prime_flats h F⟩

end Hierarchy

end OAI
