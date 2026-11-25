import OAI.Hierarchy.Conditional
import OAI.Hierarchy.GridSeparation

namespace OAI
/-! # The path, binary tree and grid give all three separations -/

namespace Hierarchy

/-- Applying the circuit row of the same border theorem to the square grid
supplies the third witness as well. -/
theorem strict_inclusions_of_graph_classification (F : Type*) [Field F]
    (graph : LowDegreeGraphTheorem F)
    (flats : ∀ d : ℕ, 0 < d → HasSpectralFlat (AlgebraicClosure (⊥ : Subfield F)) d) :
    VF F ⊂ VBP F ∧ VBP F ⊂ VP F ∧ VP F ⊂ VNP F := by
  obtain ⟨vnp, vp, _⟩ := grid_witness_separation F (graph (allHomogeneousFlats_of_flats flats)).2
  exact strict_inclusions_of_literature F graph flats
    ⟨PolynomialFamily.ofFamily (contractionFamily F SquareGrid.graph), vnp, vp⟩

end Hierarchy

end OAI
