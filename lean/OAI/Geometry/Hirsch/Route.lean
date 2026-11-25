import OAI.Geometry.Hirsch.Extension
import OAI.Geometry.Hirsch.Motions

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Forest

variable {I A : Type} {h : ℕ} (tree : Forest I A h)

def depth (i : I) := (tree.path i).length

def node (i : I) : ℕ → I
  | 0 => i
  | k+1 => ((tree.path i)[k]?).elim i Prod.fst

theorem node_next (i : I) {k : ℕ} (hk : k < tree.depth i) :
    tree.node i (k+1) = (tree.path i)[k].1 := by
  rw [node,List.getElem?_eq_getElem hk]
  rfl

theorem path_node (i : I) {k : ℕ} (hk : k ≤ tree.depth i) :
    tree.path (tree.node i k) = (tree.path i).drop k := by
  induction k with
  | zero => simp [node]
  | succ k ih =>
    have ht := ih (by omega)
    have hl : k < (tree.path i).length := hk
    rw [List.drop_eq_getElem_cons hl] at ht
    rw [node_next tree i hk]
    exact tree.proper _ _ (tree.path i)[k].2 _ ht

theorem depth_node (i : I) {k : ℕ} (hk : k ≤ tree.depth i) :
    tree.depth (tree.node i k) = tree.depth i - k := by simp [depth,path_node tree i hk]

theorem step_node (i : I) {k : ℕ} (hk : k < tree.depth i) :
    tree.path (tree.node i k) = (tree.node i (k+1),(tree.path i)[k].2) ::
      tree.path (tree.node i (k+1)) := by
  rw [path_node tree i hk.le,path_node tree i hk,node_next tree i hk]
  exact List.drop_eq_getElem_cons hk

theorem depth_card [Fintype I] (i : I) : tree.depth i + 1 ≤ Fintype.card I := by
  let f := fun k : Fin (tree.depth i + 1) => tree.node i k.val
  have hi : Function.Injective f := by
    intro a b he
    have hh := congrArg tree.depth he
    unfold f at hh
    rw [depth_node tree i (by omega),depth_node tree i (by omega)] at hh
    exact Fin.ext (by omega)
  simpa using Fintype.card_le_of_injective f hi

end OAI.Geometry.Hirsch.Forest
