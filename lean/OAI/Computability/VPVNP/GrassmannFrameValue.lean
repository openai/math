import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Completed blocks of a Grassmannian frame

The fixed columns in Lemma 5.3 come in two ordered blocks of equal size.
Adjoining a common completion produces the two planes in the ordered pair.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

open Set Submodule

variable {K V ι κ : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The span of a chosen block together with all completion columns. -/
def completedBlock {K : Type*} [Field K] [Module K V]
    (v : ι → V) (w : κ → V) (T : Set ι) : Submodule K V :=
  span K (range w) ⊔ span K (v '' T)

/-- First block of an ordered pair of independent `r`-column tuples. -/
def leftIndices (r : ℕ) : Set (Fin (r + r)) := range (Fin.castAdd r : Fin r → Fin (r + r))

/-- Second block of an ordered pair of independent `r`-column tuples. -/
def rightIndices (r : ℕ) : Set (Fin (r + r)) := range (Fin.natAdd r : Fin r → Fin (r + r))

/-- Applying a linear automorphism to the whole frame takes its completed
block to the image of the original completed block. -/
theorem completedBlock_map (v : ι → V) (w : κ → V) (T : Set ι) (e : V ≃ₗ[K] V) :
    (completedBlock v w T).map e.toLinearMap = completedBlock (e ∘ v) (e ∘ w) T := by
  simp only [completedBlock, Submodule.map_sup, Submodule.map_span,
    LinearEquiv.coe_coe, Set.range_comp, Set.image_comp]

end Grassmann

end VPVNP
end Computability
end OAI
