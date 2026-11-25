import OAI.Hierarchy.GrassmannAverages
import OAI.Hierarchy.GrassmannCube
import OAI.Computability.VPVNP.GrassmannRigidityOrbit
import OAI.Hierarchy.CubeExclusion

namespace OAI
/-! # A strict Grassmann inequality from uniform exclusion of a cube -/

namespace Hierarchy.NonlinearExpanders

open Filter HyperbolicObstruction Computability.VPVNP.Grassmann
open scoped Topology BigOperators

private theorem corner_distance {d : ℕ} (v w : CubeExclusion.Vertex d) :
    dist (CubeExclusion.corner v) (CubeExclusion.corner w) = 2 * Real.sqrt (GrassmannCube.hamming v w) := by
  have h (i : Fin d) : dist ((CubeExclusion.corner v) i) ((CubeExclusion.corner w) i) ^ 2 =
      (if v i ≠ w i then (4:ℝ) else 0) := by
    change dist (if v i then (1:ℝ) else -1) (if w i then (1:ℝ) else -1) ^ 2 = _
    cases v i <;> cases w i <;> norm_num [Real.dist_eq]
  rw [EuclideanSpace.dist_eq]
  simp only [h, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, GrassmannCube.hamming]
  rw [Real.sqrt_mul (Nat.cast_nonneg _)]
  norm_num; ring

/-- The closed limiting energy arrays inherit the quantitative cube exclusion from every target. -/
private theorem excluded_sqrt {d : ℕ} {ε : ℝ} (hε : 0 < ε) {I : Type*} (X : I → Type*)
    [∀ i, PseudoMetricSpace (X i)]
    (hex : ∀ i (x : CubeExclusion.Vertex d → X i) (r : ℝ), 0 < r → ∃ a b,
      ε ≤ |r * dist (x a) (x b) - dist (CubeExclusion.corner a) (CubeExclusion.corner b)|) :
    (fun a b : CubeExclusion.Vertex d => Real.sqrt (GrassmannCube.hamming a b)) ∉
      closure (markedDistances X _) := by
  intro hm
  obtain ⟨D,⟨i,s,hs,x,rfl⟩,hc⟩ := Metric.mem_closure_iff.mp hm (ε/2) (half_pos hε)
  obtain ⟨a,b,hab⟩ := hex i x (2*s) (by positivity)
  let Y := fun a b : CubeExclusion.Vertex d => Real.sqrt (GrassmannCube.hamming a b)
  let Z := fun a b : CubeExclusion.Vertex d => s * dist (x a) (x b)
  have hh : dist (Z a b) (Y a b) < ε/2 :=
    lt_of_le_of_lt ((dist_le_pi_dist (Z a) (Y a) b).trans (dist_le_pi_dist Z Y a)) (by simpa [dist_comm,Y,Z] using hc)
  rw [corner_distance, show 2*s*dist (x a) (x b)-2*Real.sqrt (GrassmannCube.hamming a b) =
      2 * (Z a b - Y a b) by dsimp [Y,Z]; ring, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] at hab
  rw [Real.dist_eq] at hh
  linarith

/-- The strict uniform Grassmann energy inequality in arbitrary dimension. The same positive gap
works for every CAT(0) target and every marking of the Grassmannian. -/
theorem grassmann_gap {d m : ℕ} (hd : d < m) {ε : ℝ} (hε : 0 < ε) {I : Type*} (X : I → Type*)
    [∀ i, MetricSpace (X i)] (hcat : ∀ i, CATZero (X i))
    (hex : ∀ i (x : CubeExclusion.Vertex d → X i) (r : ℝ), 0 < r → ∃ a b,
      ε ≤ |r * dist (x a) (x b) - dist (CubeExclusion.corner a) (CubeExclusion.corner b)|) :
    ∃ η > 0, ∀ (i : I) (x : Plane m → X i),
      mean (fun a b => dist (x a) (x b)^2) m ≤ ((m : ℝ)-η) * mean (fun a b => dist (x a) (x b)^2) 1 := by
  have ht (r : ℕ) := @GrassmannTransitivity.pair_transitive m r
  apply strict_grassmann_bound_of_rigidity X m (fun a b : CubeExclusion.Vertex d => (GrassmannCube.hamming a b : ℝ))
  · intro i a b t ht ht'
    obtain ⟨g,_,hg⟩ := hcat i a b
    exact ⟨g t,fun z => hg z t ⟨ht,ht'⟩⟩
  · exact excluded_sqrt hε X hex
  · intro D hD r hr
    exact GrassmannAverages.mean_le ht GrassmannCube.squares hD r hr
  · intro D hD h1 hm
    have hv := GrassmannAverages.mean_eq ht GrassmannCube.squares hD h1 hm
    refine ⟨fun v => GrassmannCube.plane (GrassmannCube.extend (m := m) v),fun v w => ?_⟩
    let r := GrassmannCube.hamming v w
    have hr : r < m := (Finset.card_le_univ _).trans_lt (by simpa using hd)
    have htype : HasType (m := m) r (GrassmannCube.plane (GrassmannCube.extend v)) (GrassmannCube.plane (GrassmannCube.extend w)) := by
      simpa [r, GrassmannCube.hamming_extend hd.le] using (GrassmannCube.plane_pair (GrassmannCube.extend (m := m) v) (GrassmannCube.extend w))
    have ho (a b c e : Plane m) (hq : IsSquare r 1 a b c e) : D a b = D c e := by
      exact (GrassmannAverages.opposite ht hD hq (by
        rw [hv (r+1) (by omega), hv r hr.le, h1]; push_cast; ring)).1
    exact (Rigidity.distance_eq_mean hr D hD.symm ho ⟨(_, _),htype⟩).trans (hv r hr.le)

end Hierarchy.NonlinearExpanders

end OAI
