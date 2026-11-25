import OAI.Computability.NearSquareRoot.CRTTableTags

/-! # One internal node of the balanced CRT permutation -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

/-- A node whose two child permutations have at most `remaining` levels. -/
structure Stage (d : ℕ) where
  node : List (Fin d)
  remaining : ℕ
  sorted : node.Pairwise (· < ·)
  capacity : node.length ≤ 2 ^ (remaining + 1)

namespace Stage

/-- The node indexed by `j` at an internal level of the full padded permutation. -/
def atLevel (d n : ℕ) (hn : n < Nat.clog 2 d)
    (j : Fin (CRTTree.level n (List.finRange d)).length) : Stage d where
  node := (CRTTree.level n (List.finRange d))[j.val]
  remaining := Nat.clog 2 d - n - 1
  sorted := (List.sortedLT_finRange d).pairwise.sublist
    (CRTTree.infix_of_mem_level (List.getElem_mem _)).sublist
  capacity := by
    apply CRTTree.length_le_of_mem_level _ (List.getElem_mem _)
    rw [List.length_finRange, ← pow_add, show (Nat.clog 2 d - n - 1 + 1) + n = Nat.clog 2 d by omega]
    exact Nat.le_pow_clog (by decide) d

variable {d : ℕ} (s : Stage d)

private theorem order_halves :
    (CRTTree.left s.node ++ CRTTree.right s.node).Pairwise (· < ·) := by
  simpa only [CRTTree.append_halves] using s.sorted

theorem disjoint :
    Disjoint (CRTTree.left s.node).toFinset (CRTTree.right s.node).toFinset := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact (lt_irrefl i) ((List.pairwise_append.mp s.order_halves).2.2 i
    (List.mem_toFinset.mp hi) i (List.mem_toFinset.mp hj))

private theorem childCapacity {node : List (Fin d)} (h : node ∈ CRTTree.children s.node) :
    node.length ≤ 2 ^ s.remaining :=
  CRTTree.length_le_of_mem_children (by simpa only [pow_succ, mul_comm] using s.capacity) h

variable (a : Fin d → ℕ) (E : Fin d → Type) [∀ i, NeZero (a i)]

/-- The left child returned by the original balanced constructor. -/
def left : CRT.BlockPerm a E (CRTTree.left s.node).toFinset :=
  (CRT.build s.remaining _ (List.pairwise_append.mp s.order_halves).1
    (s.childCapacity (by simp [CRTTree.children]))).val

/-- The right child returned by the original balanced constructor. -/
def right : CRT.BlockPerm a E (CRTTree.right s.node).toFinset :=
  (CRT.build s.remaining _ (List.pairwise_append.mp s.order_halves).2.1
    (s.childCapacity (by simp [CRTTree.children]))).val

def parent : CRT.BlockPerm a E s.node.toFinset :=
  (CRT.build (s.remaining + 1) s.node s.sorted s.capacity).val

def cross : CRT.BlockPerm a E ((CRTTree.left s.node).toFinset ∪ (CRTTree.right s.node).toFinset) :=
  CRT.shear s.disjoint (CRT.mergeOffset (s.left a E)) (CRT.mergeOffset_reads (s.left a E))

theorem left_computes : CRT.Computes (s.left a E) := (CRT.build _ _ _ _).property

theorem left_preservesTags : CRT.PreservesTags (s.left a E) := CRT.build_preservesTags _ _ _ _

omit [∀ i, NeZero (a i)] in
private theorem perm_cast {l r : Finset (Fin d)} (h : l = r)
    (p : {q : CRT.BlockPerm a E r // CRT.Computes q}) :
    ((congrArg (fun t => {q : CRT.BlockPerm a E t // CRT.Computes q}) h).mpr p).val.perm =
      p.val.perm := by
  cases h
  rfl

/-- Forgetting the support of the computed parent permutation removes the cast
along the union of the two child intervals. -/
theorem parent_perm : (s.parent a E).perm =
    ((s.left a E).parallel (s.right a E) s.disjoint).perm.trans (s.cross a E).perm := by
  rw [parent, CRT.build.eq_2]
  apply perm_cast
  rw [← List.toFinset_append, CRTTree.append_halves]

end Stage
end CRTTable

end NearSquareRoot
end Computability
end OAI
