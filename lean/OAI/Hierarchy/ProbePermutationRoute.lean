import OAI.Hierarchy.ProbeStageAllocation
import OAI.Hierarchy.ProbeStageFabric
import OAI.Hierarchy.ProbeStageScale

namespace OAI
/-! # Complete fixed-stage routing of a permutation -/

namespace Hierarchy.ProbeStage

/-- The initial, single-group matching is the supplied permutation itself. -/
def permutationTiles {n : ℕ} (π : Equiv.Perm (Fin n)) : Tiles (Fin n) Unit n where
  group _ := ()
  input := id
  output := π
  input_inj := fun _ _ h => (Prod.mk.inj h).2
  output_inj := fun _ _ h => π.injective (Prod.mk.inj h).2

def permutationFabric (h d : ℕ) : Fabric (Unit × Fin (2^h)) (Unit × Fin (2^h)) :=
  template (radix h d) (radix_pos h d) (rounds d) Unit (2^h)

/-- Greedy color choices and independently ranked ports physically route every
record from its prescribed input to the prescribed output π(x). -/
noncomputable def permutationRoute (h d : ℕ) (π : Equiv.Perm (Fin (2^h))) :
    Routes (Fin (2^h)) (permutationFabric h d) (permutationTiles π).first (permutationTiles π).last :=
  route _ _ _ (fun p => allocate p (radix_pos h d)) _ (permutationTiles π)

theorem permutation_stages (h d : ℕ) (π : Equiv.Perm (Fin (2^h))) :
    (permutationRoute h d π).layers.length = 18*(d-1)+1 := by
  have hlen := congrArg List.length (Routes.layer_shapes (permutationRoute h d π))
  rw [List.length_map] at hlen
  exact hlen.trans (by rw [permutationFabric,template_length,rounds];ring)

theorem permutation_layout (h d : ℕ) (π : Equiv.Perm (Fin (2^h))) :
    (permutationRoute h d π).layers.map RoutedLayer.shape = (permutationFabric h d).shapes :=
  Routes.layer_shapes _

end Hierarchy.ProbeStage

end OAI
