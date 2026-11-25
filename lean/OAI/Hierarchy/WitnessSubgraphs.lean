import OAI.Hierarchy.GraphProjection
import OAI.Hierarchy.BinaryTree
import OAI.Hierarchy.PathWitness

namespace OAI
/-! # Fixed paths and binary trees as subgraphs of the growing witnesses -/

namespace Hierarchy

namespace BinaryTree

/-- One child subtree of the tree of height `h+1`, including all edges within it. -/
def childEmbedding (h : ℕ) (side : Bool) : (graph h).Embedding (graph (h + 1)) where
  vertex := ⟨child side, fun _ _ h => (child_inj h).2⟩
  edge := ⟨childEdge side, fun _ _ h => congrArg Prod.snd (Sum.inr.inj h)⟩
  map_left := fun _ => rfl
  map_right := fun _ => rfl

def subtreeEmbeddingAdd (h : ℕ) : (k : ℕ) → (graph h).Embedding (graph (h + k))
  | 0 => IncidenceGraph.Embedding.id _
  | k + 1 => (childEmbedding (h + k) false).comp (subtreeEmbeddingAdd h k)

def subtreeEmbedding {h k : ℕ} (hk : h ≤ k) : (graph h).Embedding (graph k) := by
  have eqn : h + (k - h) = k := by omega
  exact eqn ▸ subtreeEmbeddingAdd h (k - h)

theorem contraction_pProjects {h k q : ℕ} (hk : h ≤ k) (hq : 0 < q)
    (F : Type*) [Field F] :
    ∃ φ : Computability.VPVNP.Projection F ((graph k).TableVar q) ((graph h).TableVar q),
      φ.hom ((graph k).contraction F q) = (graph h).contraction F q := by
  let j := subtreeEmbedding hk
  exact ⟨j.projection F ⟨0, hq⟩, j.hom_contraction F ⟨0, hq⟩⟩

end BinaryTree

namespace IncidenceGraph

/-- The first `m` vertices and `m-1` edges of a longer path. -/
def pathEmbedding {m n : ℕ} (hm : m ≤ n) : (path m).Embedding (path n) where
  vertex := Fin.castLEEmb hm
  edge := Fin.castLEEmb (Nat.sub_le_sub_right hm 1)
  map_left := fun _ => Fin.ext rfl
  map_right := fun _ => Fin.ext rfl

theorem path_contraction_pProjects {m n q : ℕ} (hm : m ≤ n) (hq : 0 < q)
    (F : Type*) [Field F] :
    ∃ φ : Computability.VPVNP.Projection F ((path n).TableVar q) ((path m).TableVar q),
      φ.hom ((path n).contraction F q) = (path m).contraction F q := by
  let j := pathEmbedding hm
  exact ⟨j.projection F ⟨0, hq⟩, j.hom_contraction F ⟨0, hq⟩⟩

end IncidenceGraph
end Hierarchy

end OAI
