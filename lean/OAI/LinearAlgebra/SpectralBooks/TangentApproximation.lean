import OAI.Geometry.HyperbolicGroups.TangentCone

/-!
# Simultaneous realization of tangent-cone distances by rescaled configurations

Each finite configuration in the completed tangent cone can be approximated
at every sufficiently small scale from the sequence `1 / (n + 1)`. Directing
these configurations by finite sets of marked points and increasing precision
gives a single pointed blowup which realizes all the tangent distances.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Topology UniformSpace HyperbolicObstruction

variable {X : Type*} [MetricSpace X] (h : CATZero X) (o : X)

/-- Every sufficiently fine rescaling approximately realizes the distances of a
given finite family in the completed tangent cone, and preserves its basepoint. -/
theorem tangentCone_finite_approx (s : Finset (TangentCone h o)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ f : TangentCone h o → X, f (TangentCone.vertex h o) = o ∧
      ∀ p ∈ s, ∀ q ∈ s,
        dist (dist (f p) (f q) / TangentCone.shrink n) (dist p q) < ε := by
  classical
  let v := TangentCone.vertex h o
  choose a ha using fun p : TangentCone h o =>
    Completion.denseRange_coe.exists_dist_lt p (show 0 < ε / 4 by positivity)
  let r (p : TangentCone h o) : TangentRay h o := if p = v then TangentRay.vertex h o else a p
  have hclose (p : TangentCone h o) : dist p (r p : TangentCone h o) < ε / 4 := by
    by_cases hp : p = v
    · subst p
      simpa [r, v, TangentCone.vertex] using (show (0 : ℝ) < ε / 4 by positivity)
    · simpa [r, hp] using ha p
  have hev (p q : TangentCone h o) : ∀ᶠ n : ℕ in atTop,
      dist (TangentCone.approxDist h o (r p) (r q) n) (dist (r p) (r q)) < ε / 2 :=
    (Metric.tendsto_nhds.mp (TangentCone.approxDist_tendsto h o (r p) (r q)))
      (ε / 2) (by positivity)
  filter_upwards [(s.eventually_all).2 (fun p _ => (s.eventually_all).2 (fun q _ => hev p q))]
    with n hn
  refine ⟨fun p => TangentCone.atScale h o (TangentCone.shrink n) (r p), ?_, ?_⟩
  · dsimp only [TangentCone.atScale, r, v]
    simp [TangentRay.vertex, (CATZero.segment_spec h o o).1]
  · intro p hp q hq
    have hnear := dist_dist_dist_le p q (r p : TangentCone h o) (r q : TangentCone h o)
    rw [Completion.dist_eq, dist_comm (dist p q)] at hnear
    change dist (TangentCone.approxDist h o (r p) (r q) n) (dist p q) < ε
    exact (dist_triangle _ (dist (r p) (r q)) _).trans_lt
      (by linarith [hn p hp q hq, hclose p, hclose q])

/-- A single net of positive rescalings realizes every tangent distance. The
maps fix the vertex, so taking one point there gives the corresponding
convergence of the rescaled distances to the basepoint. -/
theorem tangentCone_pointed_approx :
    ∃ (scale : Finset (TangentCone h o) × ℕ → ℝ)
      (point : Finset (TangentCone h o) × ℕ → TangentCone h o → X),
      (∀ i, 0 < scale i) ∧ Tendsto scale atTop (𝓝[>] 0) ∧
      (∀ i, point i (TangentCone.vertex h o) = o) ∧
      ∀ p q, Tendsto (fun i => dist (point i p) (point i q) / scale i) atTop
        (𝓝 (dist p q)) := by
  classical
  let I := Finset (TangentCone h o) × ℕ
  have hx (i : I) : ∃ k : ℕ, i.2 ≤ k ∧ ∃ f : TangentCone h o → X,
      f (TangentCone.vertex h o) = o ∧ ∀ p ∈ i.1, ∀ q ∈ i.1,
        dist (dist (f p) (f q) / TangentCone.shrink k) (dist p q) < TangentCone.shrink i.2 :=
    ((eventually_ge_atTop i.2).and
      (tangentCone_finite_approx h o i.1 (TangentCone.shrink_pos i.2))).exists
  choose k hk f hf hdist using hx
  have hsnd : Tendsto (fun i : I => i.2) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    exact (eventually_ge_atTop ((∅, n) : I)).mono fun _ hi => hi.2
  refine ⟨fun i => TangentCone.shrink (k i), f, fun i => TangentCone.shrink_pos _,
    TangentCone.shrink_tendsto.comp (tendsto_atTop_mono hk hsnd), hf, ?_⟩
  intro p q
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hsmall := ((tendsto_nhds_of_tendsto_nhdsWithin TangentCone.shrink_tendsto).comp
    hsnd).eventually (gt_mem_nhds hε)
  filter_upwards [eventually_ge_atTop (({p, q}, 0) : I), hsmall] with i hi he
  exact (hdist i p (hi.1 (by simp)) q (hi.1 (by simp))).trans he

end SpectralBooks
end LinearAlgebra
end OAI
