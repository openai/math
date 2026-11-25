import OAI.LinearAlgebra.SpectralBooks.SegmentAdditivity

/-! # Adding a triangle to a polytope

Adding a triangle and then its negative has the same effect as adding the
segments along its three oriented edges. Segment additivity and the planar
triangle law therefore force additivity upon just the first addition.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [DecidableEq E]

/-- Differences of triangle vertices are precisely the subset sums of the three
oriented edge vectors. The identity also holds for degenerate triangles. -/
theorem triangle_add_neg_eq_segments (x y z : E) :
    ({x, y, z} : Finset E) + {-x, -y, -z} =
      ({0, y - x} : Finset E) + {0, z - y} + {0, x - z} := by
  ext t
  simp only [Finset.mem_add, Finset.mem_insert, Finset.mem_singleton,
    exists_eq_or_imp, exists_eq_left, zero_add, add_zero]
  simp only [or_and_right, exists_or, exists_eq_left']
  abel_nf
  tauto

/-- For a subadditive price with exact segment additivity and the planar triangle
law, Minkowski addition of a triangle is exactly additive. -/
theorem price_add_triangle (δ : Finset E → ℝ)
    (hsubadd : ∀ (S T : Finset E), S.Nonempty → T.Nonempty → δ (S + T) ≤ δ S + δ T)
    (hsegment : ∀ (S : Finset E), S.Nonempty → ∀ v : E, δ (S + {0, v}) = δ S + ‖v‖)
    (htriangle : ∀ x y z : E, δ {x, y, z} = (dist x y + dist y z + dist z x) / 2)
    (S : Finset E) (hS : S.Nonempty) (x y z : E) :
    δ (S + {x, y, z}) = δ S + δ {x, y, z} := by
  let T : Finset E := {x, y, z}
  let U : Finset E := {-x, -y, -z}
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  have hU : U.Nonempty := Finset.insert_nonempty _ _
  have hsum : δ ((S + T) + U) = δ S + (dist x y + dist y z + dist z x) := by
    rw [add_assoc, triangle_add_neg_eq_segments, ← add_assoc, ← add_assoc]
    repeat rw [hsegment _ _ _]
    · simp only [dist_eq_norm']
      ring
    all_goals repeat first | apply Finset.Nonempty.add | exact Finset.insert_nonempty _ _ | exact hS
  have h₂ := hsubadd (S + T) U (hS.add hT) hU
  rw [hsum] at h₂
  have hpriceT := htriangle x y z
  have hpriceU := htriangle (-x) (-y) (-z)
  simp only [dist_neg_neg] at hpriceU
  change δ (S + T) = δ S + δ T
  change δ T = _ at hpriceT
  change δ U = _ at hpriceU
  exact le_antisymm (hsubadd S T hS hT) (by linarith)

end SpectralBooks
end LinearAlgebra
end OAI
