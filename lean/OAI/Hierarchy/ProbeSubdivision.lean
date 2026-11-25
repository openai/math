import OAI.Hierarchy.ProbeMaskedRoute
import OAI.Hierarchy.ProbeStageTemplateSize

namespace OAI
/-! # Subdivision of a permutation into advised, injectively routed tiles -/

namespace Hierarchy.ProbeStage

/-- The fixed mask table and layout work for every permutation. The route
carries all records through injective positions at every joint, from x to
π(x). This result bounds the actual chosen layers and actual fallback scans. -/
theorem subdivision (h d : ℕ) (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) :
    let trace := advisedRoute h d π
    trace.layers.length = 18*(d-1)+1 ∧
      trace.layers.map RoutedLayer.shape = (permutationFabric h d).shapes ∧
      (∀ l ∈ trace.layers, Shape.DyadicBounds h d l.shape) ∧
      (formatAdvice h d).inspections (radix_pos h d) (rounds d) (permutationTiles π) ≤
        rounds d*(2*4^rounds d*2^h) := by
  let trace := advisedRoute h d π
  have shape := Routes.layer_shapes trace
  have len := congrArg List.length shape
  rw [List.length_map] at len
  refine ⟨len.trans (by rw [permutationFabric,template_length,rounds];ring),shape,?_,
    permutation_inspections_linear h d hd π⟩
  intro l member
  apply template_dyadic hd l.shape
  change l.shape ∈ (permutationFabric h d).shapes
  rw [← shape]
  exact List.mem_map.mpr ⟨l,member,rfl⟩

/-- The little-o group count is uniform over all permutations and all of
their layers. -/
theorem eventually_sparse_subdivision {d : ℕ} (hd : 1≤d) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ π : Equiv.Perm (Fin (2^h)), ∀ l ∈ (advisedRoute h d π).layers,
      (Fintype.card l.shape.Group : ℝ) ≤ ε*(2:ℝ)^h := by
  filter_upwards [eventually_sparse_groups hd hε] with h bound
  intro π l mem
  apply bound l.shape
  change l.shape ∈ (permutationFabric h d).shapes
  rw [← Routes.layer_shapes (advisedRoute h d π)]
  exact List.mem_map.mpr ⟨l,mem,rfl⟩

end Hierarchy.ProbeStage

end OAI
