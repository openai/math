import OAI.Computability.NearSquareRoot.CRTTableLevelEntry
import OAI.Computability.NearSquareRoot.CRTTableStage

/-! # Packed level tables acting as the gates of the balanced CRT tree -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

variable {d : ℕ} (a w : Fin d → ℕ) {E : Fin d → Type}
  (pad : ∀ g, E g → Fin (2^w g - a g))

/-- The actual table entry of a complete level, with the child permutations,
their disjointness, and their input interval supplied by the balanced tree. -/
theorem levelTables_apply_atLevel [∀ j, NeZero (a j)] (hwidth : ∀ j, a j ≤ 2^w j)
    (hdense : ∀ j, 2^w j ≤ 2*a j) (hcop : Pairwise (fun i j => (a i).Coprime (a j)))
    (n : ℕ) (hn : n < Nat.clog 2 d) (j : Fin (CRTTree.level n (List.finRange d)).length)
    (y : CRT.Address a E) (inv : Bool) :
    let s := Stage.atLevel d n hn j
    ∀ i : Fin (CRTTree.right s.node).length,
      let g := (CRTTree.right s.node)[i.val]
      tableEntry (levelTables (levelQuery a w pad n y inv)) j.val i.val
          (coordinate (pad g) (y g)) =
        coordinate (pad g) (((bif inv then (s.cross a E).perm.symm else (s.cross a E).perm) y) g) := by
  let s := Stage.atLevel d n hn j
  exact levelTables_apply_shear a w pad hwidth hdense hcop n hn.le j y inv
    (s.left a E) (s.left_computes a E) (s.left_preservesTags a E)
    (s.right a E) (CRT.build_preservesTags _ _ _ _) s.disjoint

end CRTTable

end NearSquareRoot
end Computability
end OAI
