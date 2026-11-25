import OAI.Computability.NearSquareRoot.CRTTableLayerIndex
import OAI.Computability.NearSquareRoot.CRTTableFullLevel

/-! # Padded CRT routing by the levels of physical lookup tables -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable.Stage

/-- The executable gate rows, deepest first, with the same node order as the
table generator. Empty children retain their place in the row. -/
def bottomUp (d : ℕ) : List (List (Stage d)) :=
  (List.finRange (Nat.clog 2 d)).map fun r =>
    atDepth d (Nat.clog 2 d - 1 - r.val) (by have := r.isLt; omega)

theorem bottomUp_eq_layers (d : ℕ) :
    bottomUp d = layers (Nat.clog 2 d) (List.finRange d) (List.sortedLT_finRange d).pairwise
      (by simpa using Nat.le_pow_clog (by decide : 1 < 2) d) := by
  apply List.ext_getElem
  · simp [bottomUp]
  · intro r hr hr'
    have h : r < Nat.clog 2 d := by simpa [bottomUp] using hr
    let n := Nat.clog 2 d - 1 - r
    have hn : n < Nat.clog 2 d := by dsimp [n]; omega
    have eqv := fullLayers_getElem d n hn
    have hre : Nat.clog 2 d - 1 - n = r := by dsimp [n]; omega
    dsimp only at eqv
    rw [hre, List.getElem?_eq_getElem hr'] at eqv
    simpa [bottomUp,n] using eqv.symm

variable {d : ℕ} (a : Fin d → ℕ) (E : Fin d → Type) [∀ j, NeZero (a j)]

/-- The full bottom-up execution in lookup-table order is exactly the padded
equivalence constructed by the balanced CRT tree on all addresses. -/
theorem bottomUp_perm : layersPerm a E (bottomUp d) = CRT.paddedPermutation a E := by
  rw [bottomUp_eq_layers, layersPerm_paddedPermutation]

private theorem nodes_atDepth (n : ℕ) (hn : n < Nat.clog 2 d) :
    (atDepth d n hn).map node = CRTTree.level n (List.finRange d) := by
  apply List.ext_getElem <;> simp [atDepth,atLevel]

theorem atDepth_disjoint (n : ℕ) (hn : n < Nat.clog 2 d) :
    (atDepth d n hn).Pairwise (fun s t => s.node.Disjoint t.node) := by
  apply (List.pairwise_map (f := node)).mp
  rw [nodes_atDepth]
  apply CRTTree.pairwise_disjoint_level
  exact List.nodup_finRange _

end CRTTable.Stage

namespace CRTTable

variable {d : ℕ} (a w : Fin d → ℕ) {E : Fin d → Type}
  (pad : ∀ g, E g → Fin (2^w g - a g))

/-- Each lookup in the generated level tables gives the coordinate after
executing the entire row in the forward or inverse direction. All other nodes
of the same row operate on disjoint axes. -/
theorem levelTables_apply_row [∀ j, NeZero (a j)] (hwidth : ∀ j, a j ≤ 2^w j)
    (hdense : ∀ j, 2^w j ≤ 2*a j) (hcop : Pairwise (fun i j => (a i).Coprime (a j)))
    (n : ℕ) (hn : n < Nat.clog 2 d) (j : Fin (CRTTree.level n (List.finRange d)).length)
    (y : CRT.Address a E) (inv : Bool) :
    let s := Stage.atLevel d n hn j
    let row := Stage.layerPerm a E (Stage.atDepth d n hn)
    ∀ i : Fin (CRTTree.right s.node).length,
      let g := (CRTTree.right s.node)[i.val]
      tableEntry (levelTables (levelQuery a w pad n y inv)) j.val i.val
          (coordinate (pad g) (y g)) =
        coordinate (pad g) (((bif inv then row.symm else row) y) g) := by
  intro s row i
  let g := (CRTTree.right s.node)[i.val]
  have hg : g ∈ s.node := (List.drop_sublist ..).subset (List.getElem_mem i.isLt)
  have hs : s ∈ Stage.atDepth d n hn := List.mem_map_of_mem (f := Stage.atLevel d n hn) (by simp)
  have entry := levelTables_apply_atLevel a w pad hwidth hdense hcop n hn j y inv i
  refine entry.trans (congrArg (coordinate (pad g)) ?_)
  cases inv
  · exact (Stage.layerPerm_on a E _ (Stage.atDepth_disjoint n hn) s hs y g hg).symm
  · exact (Stage.layerPerm_symm_on a E _ (Stage.atDepth_disjoint n hn) s hs y g hg).symm

end CRTTable

end NearSquareRoot
end Computability
end OAI
