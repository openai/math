import OAI.Hierarchy.ProbeReadout

namespace OAI
/-! # Uniform local flattening of exact spectral price configurations -/

namespace Hierarchy.AdaptiveProbe
open HyperbolicObstruction LinearAlgebra.SpectralBooks Filter Topology
noncomputable section

private def signValue (s : Bool) : ℝ := if s then 1 else -1

/-- A fixed labeled finite column pattern after exact price realization. The bound K
is the radius of the pattern in its horizontal edges, independent of its axis radius. -/
structure ExactPattern (F I : Type*) [Field F] (k : ℕ) (K : ℝ) (join : I → I → Prop) where
  carrier : Type
  [metric : MetricSpace carrier]
  prices : SpectralPlacementPrices F carrier
  cat : CATZero carrier
  radius : ℝ
  positive : 0<radius
  segment : ColumnSegments I carrier k radius
  center_le : ∀ i i', dist (segment.center i) (segment.center i')≤K
  ends_le : ∀ i i' j s, dist (segment.axis i j (ColumnSegments.endTime radius s))
    (segment.axis i' j (ColumnSegments.endTime radius s))≤K
  corner : ∀ i j l, j≠l → ∀ s t, dist (segment.axis i j (ColumnSegments.endTime radius s))
    (segment.axis i l (ColumnSegments.endTime radius t))≤Real.sqrt 2*radius+1
  joined : ∀ i i', join i i' → segment.center i=segment.center i'

attribute [instance] ExactPattern.metric

variable {F I : Type*} [Field F] [Fintype I] {k : ℕ} {K : ℝ} {join : I → I → Prop}

def ExactPattern.Fits (W : ExactPattern F I k K join) (ε : ℝ) (z : I → Coordinates k) : Prop :=
  (∀ i i', join i i' → z i=z i') ∧
  (∀ i i', |dist (W.segment.center i) (W.segment.center i')-dist (z i) (z i')|<ε) ∧
  ∀ i i' j s, |max (dist (W.segment.center i) (W.segment.axis i' j (signValue s*W.radius))-W.radius) 0
    - max (signValue s*(z i' j-z i j)) 0|<ε

/-- For all sufficiently large physical radii the complete labeled ball, including all
signed endpoint readings and all horizontal identifications, has one approximate frame. -/
theorem exact_pattern_flattening (base : I) (no : ¬HasSpectralFlat F (k+1))
    {ε : ℝ} (positive : 0<ε) :
    ∃ N : ℕ, ∀ W : ExactPattern F I k K join, (N:ℝ)≤W.radius →
      ∃ z : I → Coordinates k, W.Fits ε z := by
  classical
  by_contra! failure
  choose W radius bad using failure
  let U := Ultrafilter.of (atTop : Filter ℕ)
  let A n := (W n).segment
  let P : Pattern A := {
    bounds := fun i i' => ⟨K,fun n => (W n).center_le i i',fun n => (W n).ends_le i i'⟩
    cross := fun n => (W n).corner
  }
  have escape : Tendsto (fun n => (W n).radius) (U : Filter ℕ) atTop :=
    (tendsto_atTop_mono (fun n => radius n) (tendsto_natCast_atTop_atTop (R:=ℝ))).mono_left
      (Ultrafilter.of_le _)
  obtain ⟨z,centers,ports⟩ := P.coordinates U base (fun n => (W n).prices)
    (fun n => (W n).cat) (fun n => (W n).positive) escape no
  have joins (i i' : I) (h : join i i') : z i=z i' := by
    apply dist_eq_zero.mp
    apply tendsto_nhds_unique (centers i i')
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun n => by simp [A,(W n).joined i i' h]
  have close (i i' : I) : ∀ᶠ n in (U : Filter ℕ),
      |dist ((A n).center i) ((A n).center i')-dist (z i) (z i')|<ε := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp (centers i i') ε positive
  have ends (i i' : I) (j : Fin k) (s : Bool) : ∀ᶠ n in (U : Filter ℕ),
      |max (dist ((A n).center i) ((A n).axis i' j (signValue s*(W n).radius))-(W n).radius) 0 -
        max (signValue s*(z i' j-z i j)) 0|<ε := by
    have bound : ‖z i'-z i‖≤K := by
      change dist (z i') (z i)≤K
      exact le_of_tendsto (centers i' i) (Eventually.of_forall fun n => (W n).center_le i' i)
    have lim := Pattern.endpoint_reading (A:=A) (fun n => (W n).cat) (fun n => (W n).positive)
      escape i i' j (z i) (z i') (dir:=signValue s) (by cases s <;> simp [signValue])
      bound (fun n => (W n).center_le i i') (ports i i' j)
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp (lim.max (tendsto_const_nhds (x:=0))) ε positive
  have c := eventually_all.mpr fun i => eventually_all.mpr (close i)
  have e := eventually_all.mpr fun i => eventually_all.mpr fun i' => eventually_all.mpr fun j =>
    eventually_all.mpr (ends i i' j)
  obtain ⟨n,cn,en⟩ := (c.and e).exists
  exact bad n z ⟨joins,cn,en⟩

end
end Hierarchy.AdaptiveProbe

end OAI
