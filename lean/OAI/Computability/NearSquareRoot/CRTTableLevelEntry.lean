import OAI.Computability.NearSquareRoot.CRTTableControlPacking
import OAI.Computability.NearSquareRoot.CRTTableEntry

/-! # Reading the correct shear value from a packed whole-level CRT table -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

open IntegerMultiplication IntegerMultiplication.Code

variable {d : ℕ} (a w : Fin d → ℕ) {E : Fin d → Type}
  (pad : ∀ g, E g → Fin (2^w g - a g))

def descriptor (g : Fin d) : ControlAxis := (tally (w g), tally (a g))

def addressField (y : CRT.Address a E) (g : Fin d) : List Bool :=
  (Bits.phrase (w g) (coordinate (pad g) (y g))).reverse

/-- The complete control string read by the stack program for this level in
the actual padded array. It includes every left-axis field across the level. -/
def levelQuery (n : ℕ) (y : CRT.Address a E) (inv : Bool) :=
  (inv,tally n,(List.finRange d).map (descriptor a w),
    packedControl n (List.finRange d) (addressField a w pad y))

private theorem packedNodeQuery (y : CRT.Address a E) (inv : Bool) (l r : List (Fin d)) :
    (inv,l.map (descriptor a w),r.map (descriptor a w),packFields (addressField a w pad y) l)
      = paddedMergeQuery a w pad l r y inv := by
  unfold paddedMergeQuery fieldQuery packFields
  simp only [List.flatMap_def, List.map_reverse, List.map_map, Function.comp_def]
  rfl

theorem levelTables_lookup (n : ℕ) (hn : n ≤ Nat.clog 2 d)
    (j : Fin (CRTTree.level n (List.finRange d)).length) (y : CRT.Address a E)
    (inv : Bool) :
    let node := (CRTTree.level n (List.finRange d))[j.val]
    ((levelTables (levelQuery a w pad n y inv))[j.val]?.getD []) =
      nodeTables (paddedMergeQuery a w pad (CRTTree.left node) (CRTTree.right node) y inv) := by
  have bound : n ≤ Nat.clog 2 (List.finRange d).length := by simpa using hn
  have width (i : Fin d) (_ : i ∈ List.finRange d) :
      (addressField a w pad y i).length = (descriptor a w i).1.length := by
    simp [addressField, descriptor, Bits.phrase_length]
  have h := levelTables_packed n (List.finRange d) bound (descriptor a w)
    (addressField a w pad y) inv width
  unfold levelQuery
  rw [h]
  simpa only [List.getElem?_map, List.getElem?_eq_getElem j.isLt, Option.map_some,
    Option.getD_some] using congrArg nodeTables (packedNodeQuery a w pad y inv
      (CRTTree.left ((CRTTree.level n (List.finRange d))[j.val]))
      (CRTTree.right ((CRTTree.level n (List.finRange d))[j.val])))

/-- Three explicit list lookups select the node, target axis and padded target
coordinate in the physical program's output. -/
def tableEntry (tables : List (List (List Tally))) (node axis address : ℕ) : ℕ :=
  let tablesAtNode := tables[node]?.getD []
  let targetTable := tablesAtNode[axis]?.getD []
  (targetTable[address]?.getD []).length

theorem level_node_consecutive {n : ℕ} {node : List (Fin d)}
    (hm : node ∈ CRTTree.level n (List.finRange d)) :
    ∃ start : ℕ, ∀ u : ℕ, (hu : u < (CRTTree.left node ++ CRTTree.right node).length) →
      ((CRTTree.left node ++ CRTTree.right node)[u]).val = start+u := by
  obtain ⟨start,_,h⟩ := CRTTree.finRange_node_addresses hm
  refine ⟨start, ?_⟩
  simp only [CRTTree.append_halves]
  intro u hu
  have he := congrArg (fun l : List ℕ => l[u]?) h
  simpa [List.getElem?_eq_getElem, hu] using he

theorem levelTables_apply_shear [∀ j, NeZero (a j)] (hwidth : ∀ j, a j ≤ 2^w j)
    (hdense : ∀ j, 2^w j ≤ 2*a j) (hcop : Pairwise (fun i j => (a i).Coprime (a j)))
    (n : ℕ) (hn : n ≤ Nat.clog 2 d) (j : Fin (CRTTree.level n (List.finRange d)).length)
    (y : CRT.Address a E) (inv : Bool) :
    let node := (CRTTree.level n (List.finRange d))[j.val]
    ∀ (p : CRT.BlockPerm a E (CRTTree.left node).toFinset)
      (_ : CRT.Computes p) (_ : CRT.PreservesTags p)
      (q : CRT.BlockPerm a E (CRTTree.right node).toFinset) (_ : CRT.PreservesTags q)
      (hd : Disjoint (CRTTree.left node).toFinset (CRTTree.right node).toFinset)
      (i : Fin (CRTTree.right node).length),
      let g := (CRTTree.right node)[i.val]
      let cross := CRT.shear hd (CRT.mergeOffset p) (CRT.mergeOffset_reads p)
      tableEntry (levelTables (levelQuery a w pad n y inv)) j.val i.val
          (coordinate (pad g) (y g)) =
        coordinate (pad g) (((bif inv then cross.perm.symm else cross.perm) y) g) := by
  intro node p hp tp q tq hd i
  obtain ⟨base,hpos⟩ := level_node_consecutive (List.getElem_mem j.isLt)
  unfold tableEntry
  rw [levelTables_lookup a w pad n hn j y inv]
  exact nodeTables_apply_shear a w pad hwidth hdense hcop base
    (CRTTree.left node) (CRTTree.right node) hpos p hp tp q tq hd y inv i

end CRTTable

end NearSquareRoot
end Computability
end OAI
