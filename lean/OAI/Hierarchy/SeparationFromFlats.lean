import OAI.Hierarchy.GraphWitnessBounds
import OAI.Hierarchy.FixedGridCircuit
import OAI.Hierarchy.PaperBounds

namespace OAI
/-! # All arithmetic consequences from the common prime-field hypothesis -/

namespace Hierarchy

open LinearAlgebra.SpectralBooks

/-- The path, binary tree and square grid have independently proved lower
bounds on homogeneous flats. The graph-classification theorem is thereby
discharged for all the witnesses needed by the class separation. -/
theorem separations_of_prime_flats (flats : UnboundedPrimeFieldFlats) (F : Type*) [Field F] :
    VF F ⊂ VBP F ∧ VBP F ⊂ VP F ∧ VP F ⊂ VNP F := by
  have hom : AllHomogeneousFlats (AlgebraicClosure (⊥ : Subfield F)) :=
    allHomogeneousFlats_of_flats (fun d _ => flats.all_dimensions _ d)
  obtain ⟨⟨abp, formula, _⟩, ⟨circuit, treeABP, _⟩⟩ := graph_witness_bounds F hom
  obtain ⟨vnp, gridVP, _⟩ := grid_witness_of_flats F hom
  exact strict_inclusions_of_witnesses F
    ⟨PolynomialFamily.ofFamily (contractionFamily F IncidenceGraph.path),abp,formula⟩
    ⟨PolynomialFamily.ofFamily (contractionFamily F completeBinaryTrees),circuit,treeABP⟩
    ⟨PolynomialFamily.ofFamily (contractionFamily F SquareGrid.graph),vnp,gridVP⟩

/-- All three explicit graph witnesses and the square formal exponent now
share a single premise concerning spectral flats over the prime fields. -/
theorem paper_bounds_of_spectral_flats (flats : UnboundedPrimeFieldFlats)
    (F : Type*) [Field F] :
    (VF F ⊂ VBP F ∧ VBP F ⊂ VP F ∧ VP F ⊂ VNP F) ∧
    2 * Real.exp (stdNormalQuantile (2 / 3) ^ 2 / 2) ≤ formalOmega F 1 1 1 ∧
    (1097 : ℝ)/500 < formalOmega F 1 1 1 :=
  ⟨separations_of_prime_flats flats F,square_exponent_of_prime_flats flats F⟩


end Hierarchy

end OAI
