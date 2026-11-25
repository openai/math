import OAI.LinearAlgebra.SpectralBooks.SectorTriangleSeminorm

/-! # The seminorm on the parameter quadrant of an unbounded sector -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set

variable {X : Type*} [PseudoMetricSpace X]

/-- The distance on a Busemann convex affine sector extends to a seminorm
on the difference space of its parameters. -/
theorem quadrant_seminorm_of_affine (H : (ℝ × ℝ) → X)
    (hseg : ∀ p q : ℝ × ℝ, 0 ≤ p → 0 ≤ q → ∀ t : ℝ, t ∈ Icc 0 1 →
      dist (H p) (H ((1 - t) • p + t • q)) = t * dist (H p) (H q))
    (hcon : ∀ z p q : ℝ × ℝ, 0 ≤ z → 0 ≤ p → 0 ≤ q → ∀ t : ℝ, t ∈ Icc 0 1 →
      dist (H ((1-t) • z + t • p)) (H ((1-t) • z + t • q)) ≤ t * dist (H p) (H q)) :
    ∃ N : Seminorm ℝ (ℝ × ℝ), ∀ p q, 0 ≤ p → 0 ≤ q → dist (H p) (H q) = N (p - q) := by
  have hC : Convex ℝ (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)) :=
    (convex_Ici _).prod (convex_Ici _)
  have hI : (interior (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ))).Nonempty := by
    refine ⟨(1,1), ?_⟩
    rw [interior_prod_eq, interior_Ici]
    change 0 < (1 : ℝ) ∧ 0 < (1 : ℝ)
    norm_num
  obtain ⟨N, hN⟩ := convex_seminorm_of_affine hC hI H
    (fun p hp q hq ↦ hseg p q hp hq) (fun z hz p hp q hq ↦ hcon z p q hz hp hq)
  exact ⟨N, fun p q hp hq ↦ hN p hp q hq⟩

end SpectralBooks
end LinearAlgebra
end OAI
