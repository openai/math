import OAI.Hierarchy.ProbeAltimeter
import OAI.Hierarchy.ProbeLimit

namespace OAI
/-! # Long physical readings converge to the signed coordinates of the shared frame -/

namespace Hierarchy.AdaptiveProbe
open HyperbolicObstruction LinearAlgebra.SpectralBooks Filter Topology
open scoped InnerProductSpace
noncomputable section

private theorem move_eq {k : ℕ} (z : Coordinates k) (j : Fin k) (r s : ℝ) :
    move z j (s*r) = z+r • EuclideanSpace.single j s := by
  ext l
  by_cases h : l=j
  · subst l
    simp [move,mul_comm]
  · simp [move,h]

private theorem move_reading {k : ℕ} (u v : Coordinates k) (j : Fin k) {dir r : ℝ}
    (sign : dir=1 ∨ dir= -1) (hr : ‖v-u‖<r) :
    let e := dist u (move v j (dir*r))-r
    0≤e-dir*(v j-u j) ∧ e-dir*(v j-u j)≤‖v-u‖^2/(2*(r-‖v-u‖)) := by
  let d := EuclideanSpace.single j dir
  have unit : ‖d‖=1 := by
    rw [PiLp.norm_single,Real.norm_eq_abs]
    rcases sign with e|e <;> simp [e]
  have inner : ⟪v-u,d⟫_ℝ=dir*(v j-u j) := by
    rw [EuclideanSpace.inner_single_right]
    simp []
  have diff : dist u (move v j (dir*r))=‖(v-u)+r • d‖ := by
    rw [dist_comm,dist_eq_norm,move_eq]
    congr 1
    abel
  dsimp only
  rw [diff,←inner]
  exact euclidean_readout (v-u) d unit hr

/-- Passing a radius to infinity with a uniform finite-radius comparison. -/
private theorem physical_tendsto {U : Ultrafilter ℕ} {target K : ℝ} {large : ℕ → ℝ}
    {near : ℝ → ℕ → ℝ} {value : ℝ → ℝ} (hK : 0≤K)
    (fixed : ∀ r, 0<r → Tendsto (near r) (U : Filter ℕ) (𝓝 (value r)))
    (accuracy : ∀ r, K<r → 0≤value r-target ∧ value r-target≤K^2/(2*(r-K)))
    (tail : ∀ r, 0<r → ∀ᶠ n in (U : Filter ℕ), 0≤near r n-large n ∧ near r n-large n≤K^2/(2*r)) :
    Tendsto large (U : Filter ℕ) (𝓝 target) := by
  apply Metric.tendsto_nhds.mpr
  intro ε he
  let r := K + (K^2+1)/ε + 1
  have kpos : 0<(K^2+1)/ε := div_pos (by positivity) he
  have far : K<r := by dsimp [r]; linarith
  have pos := hK.trans_lt far
  have ratio := div_mul_cancel₀ (K^2+1) he.ne'
  have a : K^2/(2*(r-K))<ε/2 := by
    apply (div_lt_iff₀ (by linarith : 0<2*(r-K))).mpr
    dsimp only [r]
    nlinarith only [ratio,he]
  have b : K^2/(2*r)≤K^2/(2*(r-K)) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith)
  have close := (Metric.tendsto_nhds.mp (fixed r pos)) (ε/2) (by positivity)
  filter_upwards [close,tail r pos] with n hn htail
  rw [Real.dist_eq,abs_lt] at hn ⊢
  obtain ⟨al,ar⟩ := accuracy r far
  constructor <;> linarith [hn.1,hn.2,htail.1,htail.2]

namespace Pattern
variable {I : Type*} {X : ℕ → Type} [∀ n, MetricSpace (X n)] {k : ℕ} {R : ℕ → ℝ}
variable {A : ∀ n, ColumnSegments I (X n) k (R n)} {U : Ultrafilter ℕ}

theorem endpoint_reading (C : ∀ n, CATZero (X n)) (hR : ∀ n, 0<R n)
    (escape : Tendsto R (U : Filter ℕ) atTop) (i i' : I) (j : Fin k)
    (u v : Coordinates k) {dir K : ℝ} (sign : dir=1 ∨ dir= -1)
    (hK : ‖v-u‖≤K) (hcentr : ∀ n, dist ((A n).center i) ((A n).center i')≤K)
    (coords : ∀ s, Tendsto (fun n => dist ((A n).center i) ((A n).axis i' j s))
      (U : Filter ℕ) (𝓝 (dist u (move v j s)))) :
    Tendsto (fun n => dist ((A n).center i) ((A n).axis i' j (dir*R n))-R n)
      (U : Filter ℕ) (𝓝 (dir*(v j-u j))) := by
  let d := ‖v-u‖
  have nonneg := (norm_nonneg _).trans hK
  apply physical_tendsto (K:=K) (near:=fun r n => dist ((A n).center i) ((A n).axis i' j (dir*r))-r)
    (value:=fun r => dist u (move v j (dir*r))-r) nonneg
  · intro r _
    exact (coords (dir*r)).sub tendsto_const_nhds
  · intro r far
    obtain ⟨lo,hi⟩ := move_reading u v j sign (hK.trans_lt far)
    refine ⟨lo,hi.trans ?_⟩
    exact (div_le_div_of_nonneg_left (sq_nonneg _) (by linarith : 0<2*(r-K)) (by linarith)).trans
      (div_le_div_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) nonneg).2 hK) (by linarith))
  · intro r hr
    filter_upwards [escape.eventually_ge_atTop r] with n hn
    have absdir : |dir|=1 := by rcases sign with e|e <;> simp [e]
    have ds : |dir*r|=r := by rw [abs_mul,absdir,one_mul,abs_of_pos hr]
    have dR : |dir*R n|=R n := by rw [abs_mul,absdir,one_mul,abs_of_pos (hR n)]
    have side : ColumnSegments.endTime (R n) (dir*r)=dir*R n := by
      rcases sign with e|e
      · simp [ColumnSegments.endTime,e,hr.le]
      · simp [ColumnSegments.endTime,e,not_le.mpr (neg_neg_of_pos hr)]
    have len : dist ((A n).center i') ((A n).axis i' j (dir*R n))=R n := by
      rw [←(A n).starts i' j,(A n).intrinsic i' j _ _ (by simpa using (hR n).le) dR.le,
        zero_sub,abs_neg,dR]
    have hseg := (A n).radial (C n) (hR n) i' j (dir*r) (ds.trans_le hn)
    rw [ds,side] at hseg
    have tail := segment_readout (C n) ((A n).center i') ((A n).axis i' j (dir*R n))
      ((A n).center i) len hr hn
    dsimp only at tail
    rw [←hseg] at tail
    exact ⟨tail.1,tail.2.trans (div_le_div_of_nonneg_right
      ((sq_le_sq₀ dist_nonneg nonneg).2 (hcentr n)) (by positivity))⟩

end Pattern
end
end Hierarchy.AdaptiveProbe

end OAI
