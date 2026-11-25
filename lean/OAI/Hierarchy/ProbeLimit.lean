import OAI.Hierarchy.ProbeSegments
import OAI.Hierarchy.ProbeFrame
import OAI.Hierarchy.ProbePerpendicular
import OAI.LinearAlgebra.SpectralBooks.SpectralMetricLimit

namespace OAI
/-! # Common signed axes for a finite pattern of increasingly long column segments -/

namespace Hierarchy.AdaptiveProbe
open HyperbolicObstruction LinearAlgebra.SpectralBooks Filter Topology MetricLimit
noncomputable section

variable {I : Type*} {X : ℕ → Type} [∀ n, MetricSpace (X n)] {k : ℕ} {R : ℕ → ℝ}

structure Pattern (A : ∀ n, ColumnSegments I (X n) k (R n)) : Prop where
  bounds : ∀ i i', ∃ K : ℝ, (∀ n, dist ((A n).center i) ((A n).center i')≤K) ∧
    ∀ n j s, dist ((A n).axis i j (ColumnSegments.endTime (R n) s))
      ((A n).axis i' j (ColumnSegments.endTime (R n) s)) ≤ K
  cross : ∀ n i j l, j≠l → ∀ s t, dist ((A n).axis i j (ColumnSegments.endTime (R n) s))
    ((A n).axis i l (ColumnSegments.endTime (R n) t)) ≤ Real.sqrt 2*R n+1

namespace Pattern
variable (U : Ultrafilter ℕ) (base : I) {A : ∀ n, ColumnSegments I (X n) k (R n)} (P : Pattern A)

def centerRep (i : I) : Bounded U X (fun n => (A n).center base) :=
  ⟨fun n => (A n).center i,by obtain ⟨K,bd,_⟩ := P.bounds base i; exact ⟨K,bd⟩⟩

def axisRep (i : I) (j : Fin k) (s : ℝ) : Bounded U X (fun n => (A n).center base) :=
  ⟨fun n => (A n).axis i j s,by
    obtain ⟨K,bd,_⟩ := P.bounds base i
    exact ⟨K+|s|,fun n => (dist_triangle _ ((A n).center i) _).trans
      (add_le_add (bd n) ((A n).bounded i j s))⟩⟩

/-- Comparing signed ports in finite columns produces genuine parallel, perpendicular lines.
The radius-dependent ceiling error vanishes in the ultralimit. -/
def axes (C : ∀ n, CATZero (X n)) (hR : ∀ n, 0<R n)
    (escape : Tendsto R (U : Filter ℕ) atTop) :
    Axes I (Space (U:=U) (X:=X) (o:=fun n => (A n).center base)) k := by
  let a i j t := point (P.axisRep U base i j t)
  let c i := point (P.centerRep U base i)
  have origin (i : I) (j : Fin k) : a i j 0=c i := by
    change point (P.axisRep U base i j 0)=point (P.centerRep U base i)
    congr 1
    apply Bounded.ext
    funext n
    exact (A n).starts i j
  have iso (i : I) (j : Fin k) : Isometry (a i j) := by
    apply Isometry.of_dist_eq
    intro s t
    apply tendsto_nhds_unique (tendsto_point_dist (P.axisRep U base i j s) (P.axisRep U base i j t))
    apply tendsto_const_nhds.congr'
    filter_upwards [escape.eventually_ge_atTop |s|,escape.eventually_ge_atTop |t|] with n hs ht
    exact (Real.dist_eq ..).trans ((A n).intrinsic i j s t hs ht).symm
  refine ⟨c,a,origin,iso,?_,?_⟩
  · intro i j l jl
    apply perpendicular_of_equal_radius (MetricLimit.catZero C) _ _ (iso i j) (iso i l)
      ((origin i j).trans (origin i l).symm)
    intro s t same
    have ht : Tendsto (fun n => Real.sqrt 2*|s|+|s|/R n) (U : Filter ℕ) (𝓝 (Real.sqrt 2*|s|)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x:=Real.sqrt 2*|s|)).add
        ((tendsto_const_nhds (x:=|s|)).div_atTop escape)
    have bound := le_of_tendsto_of_tendsto
      (tendsto_point_dist (P.axisRep U base i j s) (P.axisRep U base i l t)) ht (by
        filter_upwards [escape.eventually_ge_atTop |s|] with n hs
        exact (A n).cross_le (C n) (hR n) i j l s t hs same (P.cross n i j l jl s t))
    have sq := sq_le_sq₀ dist_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (abs_nonneg s)) |>.2 bound
    rw [mul_pow,Real.sq_sqrt (by norm_num),sq_abs] at sq
    have eqq := congrArg (fun q : ℝ => q^2) same
    simp only [sq_abs] at eqq
    nlinarith
  · intro i i' j
    obtain ⟨K,centers,ends⟩ := P.bounds i i'
    refine ⟨K,fun s => le_of_tendsto (tendsto_point_dist (P.axisRep U base i j s)
      (P.axisRep U base i' j s)) ?_⟩
    filter_upwards [escape.eventually_ge_atTop |s|] with n hs
    exact (A n).parallel_le (C n) (hR n) i i' j s K hs (centers n) (ends n j s)

include P base in
/-- Uniformly bounded centers acquire one Euclidean coordinate frame. The same frame
recovers every finite-parameter signed port distance in the original finite patterns. -/
theorem coordinates {F : Type*} [Field F] (prices : ∀ n, SpectralPlacementPrices F (X n))
    (C : ∀ n, CATZero (X n)) (hR : ∀ n, 0<R n) (escape : Tendsto R (U : Filter ℕ) atTop)
    (no : ¬ HasSpectralFlat F (k+1)) :
    ∃ z : I → Coordinates k, (∀ i i', Tendsto (fun n => dist ((A n).center i) ((A n).center i'))
      (U : Filter ℕ) (𝓝 (dist (z i) (z i')))) ∧
      ∀ i i' j s, Tendsto (fun n => dist ((A n).center i) ((A n).axis i' j s))
        (U : Filter ℕ) (𝓝 (dist (z i) (move (z i') j s))) := by
  let axes := P.axes U base C hR escape
  obtain ⟨z,centers,ports⟩ := exact_column_coordinates base
    (SpectralPlacementPrices.metricLimit (o:=fun n => (A n).center base) U prices)
    (MetricLimit.catZero C) no axes
  refine ⟨z,?_,?_⟩
  · intro i i'
    rw [←centers i i']
    exact tendsto_point_dist (P.centerRep U base i) (P.centerRep U base i')
  · intro i i' j s
    rw [←ports i i' j s]
    exact tendsto_point_dist (P.centerRep U base i) (P.axisRep U base i' j s)

end Pattern
end
end Hierarchy.AdaptiveProbe

end OAI
