import OAI.Hierarchy.CubeExclusion

namespace OAI
/-! # The transverse factor in a maximal Euclidean spectral flat -/

namespace Hierarchy.AdaptiveProbe
open MatrixMultiplication LinearAlgebra.SpectralBooks HyperbolicObstruction
open CubeExclusion
noncomputable section

private def sign (v : Bool) : ℝ := if v then 1 else -1

private theorem split_corner {k : ℕ} (i j : Vertex (k+1)) :
    dist (corner i) (corner j)^2 =
      (sign (i 0)-sign (j 0))^2 +
        dist (corner (i ∘ Fin.succ)) (corner (j ∘ Fin.succ))^2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_succ, EuclideanSpace.dist_sq_eq]
  simp only [Real.dist_eq,sq_abs]
  rfl

/-- The marked corners of a spectral product with a nontrivial transverse
factor realize the next Euclidean cube after a single common rescaling.
Only the two transverse points are used. -/
theorem transverse_subsingleton {F : Type*} [Field F] {k : ℕ}
    {X : Type} [MetricSpace X] (P : SpectralPlacementPrices F X) (hX : CATZero X)
    (no : ¬ HasSpectralFlat F (k+1)) {Y : Type*} [MetricSpace Y]
    (e : EuclideanSpace ℝ (Fin k) → Y → X)
    (prod : ∀ u v p q, dist (e u p) (e v q)^2 = dist u v^2 + dist p q^2) :
    Subsingleton Y := by
  constructor
  intro p q
  by_contra hp
  let L := dist p q / 2
  have pos : 0 < L := half_pos (dist_pos.mpr hp)
  let transverse (i : Vertex (k+1)) := if i 0 then q else p
  let flat (i : Vertex (k+1)) := corner (i ∘ Fin.succ)
  let mark (i : Vertex (k+1)) := e (L • flat i) (transverse i)
  have width (i j : Vertex (k+1)) : dist (transverse i) (transverse j)^2 =
      L^2*(sign (i 0)-sign (j 0))^2 := by
    cases hi : i 0 <;> cases hj : j 0 <;> simp [transverse,sign,hi,hj,L,dist_comm q p] <;> ring
  have metric (i j : Vertex (k+1)) :
      dist (mark i) (mark j) = L * dist (corner i) (corner j) := by
    apply (sq_eq_sq₀ dist_nonneg (mul_nonneg pos.le dist_nonneg)).mp
    change dist (e (L • flat i) (transverse i)) (e (L • flat j) (transverse j))^2 = _
    rw [prod,width,dist_smul₀,Real.norm_eq_abs,abs_of_pos pos,mul_pow,mul_pow,split_corner]
    dsimp only [flat]
    ring
  obtain ⟨ε, hε, gap⟩ := uniform_gap no
  obtain ⟨i,j,err⟩ := gap X P hX mark L⁻¹ (inv_pos.mpr pos)
  rw [metric,←mul_assoc,inv_mul_cancel₀ pos.ne',one_mul,sub_self,abs_zero] at err
  exact (not_lt_of_ge err) hε

end
end Hierarchy.AdaptiveProbe

end OAI
