import OAI.Hierarchy.GridLensPaths
import OAI.Hierarchy.GridLensSegments

namespace OAI
/-! # The geometry budget of the actual equality tests and mounted catalysts

A finite test list supplies one demand for each equality, even if several tests
are colocated. Each mounted catalyst pair supplies the demand from its negative
to its positive port. The path certificate places each leg on a particular rail
segment or proves its endpoints coincide.
-/

namespace Hierarchy.GridLens
open scoped BigOperators
noncomputable section

variable {k n E L q : ℕ}

/-- A path for each physical charge in one wiring, using the chosen rail segments. -/
abbrev PathCertificate {A : Type*} (direction : Fin E → Fin k) (row : Fin E → Fin k → Fin (n+1))
    (R : ℝ) (ends : A → Bool → EuclideanSpace ℝ (Fin k)) :=
  SegmentPaths ends (fun z : Fin E × Segment n => segmentEnd (direction z.1) (row z.1) R z.2)

/-- A demand is an actual equality occurrence or a specified catalyst wire in a cell. -/
abbrev Demand (q L : ℕ) (width : Fin k → ℕ) := Fin q ⊕ (Fin L × (Σ j, Fin (width j)))

/-- Endpoints on the observed equality tests and the translated catalyst ports. -/
def demandEnds (width : Fin k → ℕ) (cell : Fin L → Fin k → Fin (n+1))
    (eqAt : Fin q → Bool → EuclideanSpace ℝ (Fin k)) : Demand q L width → Bool → EuclideanSpace ℝ (Fin k)
  | .inl e => eqAt e
  | .inr (c, ⟨j, _⟩) => cellPort (cell c) j

/-- Charging each equality and each catalyst pair to actual rail segments proves the wire budget.
Here `q` can be the length of the equality list of an arbitrary selected wiring. -/
theorem equality_cost_add_catalysts_le (direction : Fin E → Fin k) (row : Fin E → Fin k → Fin (n+1))
    (R : ℝ) (width : Fin k → ℕ) (cell : Fin L → Fin k → Fin (n+1))
    (eqAt : Fin q → Bool → EuclideanSpace ℝ (Fin k))
    (paths : PathCertificate direction row R (demandEnds width cell eqAt)) :
    (∑ e, dist (eqAt e false) (eqAt e true)) + (∑ _c : Fin L, 2 * ∑ j, (width j : ℝ)) ≤
      ∑ e, railCost (direction e) (row e) R := by
  have lens := paths.sum_dist_le
  rw [Fintype.sum_sum_type] at lens
  simp only [Fintype.sum_prod_type, demandEnds, dist_cellPort,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sum_segment_dist] at lens
  simpa [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using lens


end
end Hierarchy.GridLens

end OAI
