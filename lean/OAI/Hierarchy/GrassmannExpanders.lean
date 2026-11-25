import OAI.Hierarchy.NonlinearKernelFamily
import OAI.Hierarchy.GrassmannSampling

namespace OAI
/-! # Nonlinear expanders from a strict mid-dimensional Grassmann gap -/

namespace Hierarchy.NonlinearExpanders

open ThreeFlat.Expander
open HyperbolicObstruction Computability.VPVNP.Grassmann

universe u v

/-- A common strict Grassmann inequality on a class of complete CAT(0)
targets gives one family of connected, loopless, fixed-degree graphs
of unbounded dyadic order. -/
theorem expanders_of_grassmann_gap {m : ℕ} (hm : 2 ≤ m) {b : ℝ} (hb : 0 ≤ b) (hbm : b < m)
    {I : Type v} (X : I → Type u) [∀ i, MetricSpace (X i)] [∀ i, CompleteSpace (X i)]
    (cat : ∀ i, CATZero (X i))
    (grass : ∀ i (y : Plane m → X i), mean (fun U V => dist (y U) (y V)^2) m ≤
        b * mean (fun U V => dist (y U) (y V)^2) 1) :
    ∃ (h : ℕ) (γ : ℝ), 0 < h ∧ 0 ≤ γ ∧
      ∀ n₀ : ℕ, ∃ n ≥ n₀, ∃ G : Graph n h, ∀ i, Bound (transition G.arcs h) (X i) γ := by
  have hp : 0 < m := by omega
  let : Nonempty (Pair m 1) := GrassmannSampling.adjacent_nonempty hp
  apply expanders_of_matched_partitions (J := Pair m 1) hm hb hbm X cat
  intro n
  obtain ⟨e,f,all⟩ := GrassmannSampling.exists_paired_layouts.{u} m n hp
  exact ⟨e,f,fun i => all (X i) b (grass i)⟩

end Hierarchy.NonlinearExpanders

end OAI
