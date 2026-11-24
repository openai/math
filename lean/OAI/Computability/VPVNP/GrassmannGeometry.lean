import OAI.Computability.VPVNP.GrassmannFourPoint

/-!
# CAT(0) quadrilaterals

The proof of Lemma 5.3 of *VP and VNP differ over every field* averages
the squared quadrilateral inequality over subspace rectangles. At equality
both pairs of opposite sides have equal lengths.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

variable {X : Type*} [PseudoMetricSpace X]

private theorem distance_quadBounds (h : HasCATZeroSegments X) :
    Grassmann.QuadBounds (fun a b : X => dist a b ^ 2) := by
  have hbound := Grassmann.quadBounds_of_mem_catZeroArrays
    (Grassmann.scaledDistSq_mem_catZeroArrays h (id : X → X) zero_le_one)
  simpa only [id_eq, one_mul] using hbound

/-- The squared quadrilateral inequality (4.3), with cyclic vertices `a,b,c,d`. -/
theorem quadrilateral_sq (h : HasCATZeroSegments X) (a b c d : X) :
    dist a c ^ 2 + dist b d ^ 2 ≤
      dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2 :=
  (distance_quadBounds h).quad a b c d

/-- Equality of the squared diagonals and sides forces equality of opposite
side lengths, as used in the Grassmannian rigidity argument. -/
theorem quadrilateral_eq_opposite (h : HasCATZeroSegments X) (a b c d : X)
    (heq : dist a c ^ 2 + dist b d ^ 2 =
      dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2) :
    dist a b = dist c d ∧ dist b c = dist d a := by
  obtain ⟨hab, hbc⟩ := (distance_quadBounds h).opposite a b c d heq
  exact ⟨(sq_eq_sq₀ dist_nonneg dist_nonneg).mp hab, (sq_eq_sq₀ dist_nonneg dist_nonneg).mp hbc⟩

end SpectralGeometry

end VPVNP
end Computability
end OAI
