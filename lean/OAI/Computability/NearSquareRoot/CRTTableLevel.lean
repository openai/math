import OAI.Computability.NearSquareRoot.CRTTableBatch
import OAI.Computability.NearSquareRoot.CRTTableNode
import OAI.Computability.NearSquareRoot.CRTTableInputSize
import OAI.Computability.NearSquareRoot.CRTTree
import OAI.Computability.IntegerMultiplication.Carry.Shrink

/-! # Constructing the balanced CRT level on stacks

The program halves the number of axes in every interval using a unary ruler.
It stops subdividing once the number of nodes reaches the number of axes.
This keeps setup polynomial on every binary tape input even when the caller
supplies a depth past the last meaningful level.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable
open IntegerMultiplication IntegerMultiplication.Code

private def halves (xs : List ControlAxis) : LevelBlock :=
  cutLists ((Carry.half (ruler xs)).1, xs)

private theorem halves_easy : Easy halves :=
  easy_cut (((Easy.ruler Easy.identity).compose Carry.halfCost).fstCompose.pair Easy.identity)

private theorem halves_eq (xs : List ControlAxis) :
    halves xs = (CRTTree.left xs,CRTTree.right xs) := by
  simp [halves, Carry.half_v, cutLists, CRTTree.left, CRTTree.right]

private def descend (nodes : List (List ControlAxis)) : List (List ControlAxis) :=
  nodes.flatMap CRTTree.children

private theorem descend_easy : Easy descend := by
  have h := halves_easy.compose (show Easy (fun p : LevelBlock => [p.1,p.2]) by fun_prop)
  have he : (fun a : List ControlAxis => [(halves a).1,(halves a).2]) = CRTTree.children := by
    funext a
    rw [halves_eq]
    rfl
  rw [he] at h
  exact h.mapping.compose Easy.flatten

private theorem descend_length (nodes : List (List ControlAxis)) :
    (descend nodes).length = 2 * nodes.length := by
  induction nodes with
  | nil => rfl
  | cons h t ih =>
    change (CRTTree.children h ++ descend t).length = _
    simp [CRTTree.children, ih, Nat.mul_add]

private theorem descend_flatten (nodes : List (List ControlAxis)) :
    (descend nodes).flatten = nodes.flatten := by
  induction nodes with
  | nil => rfl
  | cons h t ih =>
    change (CRTTree.children h ++ descend t).flatten = _
    simp [CRTTree.children, ih, ← List.append_assoc]

private theorem nestedSize (nodes : List (List ControlAxis)) :
    size nodes = size nodes.flatten + 2 * nodes.length := by
  induction nodes with
  | nil => rfl
  | cons x t ih =>
    simp only [size_cons, List.flatten_cons, List.length_cons, ih]
    have := size_append_right x t.flatten
    omega

private def splitUntil (p : Tally × List (List ControlAxis)) :=
  bif Iter.small (p.2,p.1) then descend p.2 else p.2

private theorem splitUntil_poly : Poly splitUntil :=
  Poly.choose (Easy.exchange.compose Iter.small_easy).poly
    (Easy.snd.compose descend_easy).poly Easy.snd.poly

private theorem splitUntil_size (cap : Tally) (nodes : List (List ControlAxis)) :
    size (splitUntil (cap,nodes)) ≤ 2 * size cap + size nodes := by
  by_cases h : nodes.length < cap.length
  · simp only [splitUntil, Iter.small, h, decide_true, Bool.cond_true, nestedSize,
      descend_flatten, descend_length, size_tally]
    omega
  · simp [splitUntil, Iter.small, h]

private def atDepth (p : Tally × List ControlAxis) :=
  ((fun nodes => splitUntil (ruler p.2,nodes))^[p.1.length]) [p.2]

private theorem atDepth_poly : Poly atDepth := by
  have h := Poly.bounder splitUntil splitUntil_poly 2 splitUntil_size
  have he : Poly (fun p : Tally × List ControlAxis => (p.1,ruler p.2,[p.2])) :=
    (show Easy (fun p : Tally × List ControlAxis => (p.1,ruler p.2,[p.2])) by fun_prop).poly
  exact he.compose h

private theorem level_node_count (xs : List ControlAxis) (t : ℕ) :
    (CRTTree.level t xs).length = 2^t := by
  induction t with
  | zero => simp [CRTTree.level]
  | succ t ih =>
    change (descend (CRTTree.level t xs)).length = _
    rw [descend_length, ih, pow_succ']

private theorem atDepth_eq (xs : List ControlAxis) (n : ℕ) (hn : n ≤ Nat.clog 2 xs.length) :
    ((fun nodes => splitUntil (ruler xs,nodes))^[n]) [xs] = CRTTree.level n xs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have h := Nat.pow_lt_of_lt_clog (b := 2) (by omega : n < Nat.clog 2 xs.length)
    simp [splitUntil, Iter.small, level_node_count, h, descend, CRTTree.level]

/-- Left control and right target descriptors in the order used by the batch
table constructor. -/
def levelBlocks (p : Tally × List ControlAxis) : List LevelBlock :=
  (atDepth p).map halves

theorem levelBlocks_poly : Poly levelBlocks :=
  atDepth_poly.compose (Poly.maps halves halves_easy.poly)

theorem levelBlocks_eq (xs : List ControlAxis) (n : ℕ) (hn : n ≤ Nat.clog 2 xs.length) :
    levelBlocks (tally n,xs) =
      (CRTTree.level n xs).map (fun node => (CRTTree.left node,CRTTree.right node)) := by
  simp only [levelBlocks, atDepth, tally_length, atDepth_eq xs n hn]
  exact congrArg (fun f => (CRTTree.level n xs).map f) (funext halves_eq)

/-- Generate every local table from the box descriptors, the depth, and the
complete control word, charging the split and the per-node calls together. -/
theorem levelBatch_poly {Y : Type} [Codec Y] {f : (Bool × LocalControl) → Y}
    (h : Poly f) :
    Poly (fun p : Bool × Tally × List ControlAxis × List Bool =>
      batchTables f (p.1,levelBlocks (p.2.1,p.2.2.1),p.2.2.2)) := by
  have hb := (show Poly (fun p : Bool × Tally × List ControlAxis × List Bool =>
      (p.2.1,p.2.2.1)) by fun_prop).compose levelBlocks_poly
  exact ((show Poly (fun p : Bool × Tally × List ControlAxis × List Bool => p.1) by fun_prop).pair
    (hb.pair (by fun_prop))).compose (batchTables_poly h)

/-- Tables for the entire depth. Every target table is a list of unary output
indices indexed by padded input coordinates. -/
def levelTables (p : Bool × Tally × List ControlAxis × List Bool) : List (List (List Tally)) :=
  batchTables nodeTables (p.1,levelBlocks (p.2.1,p.2.2.1),p.2.2.2)

theorem levelTables_poly : Poly levelTables := levelBatch_poly nodeTables_poly

theorem levelTables_getElem (xs : List ControlAxis) (n : ℕ) (hn : n ≤ Nat.clog 2 xs.length)
    (inverse : Bool) (segs : List (LevelBlock × List Bool))
    (nodes : segs.map Prod.fst =
      (CRTTree.level n xs).map (fun a => (CRTTree.left a, CRTTree.right a)))
    (width : ∀ s ∈ segs, s.2.length = (leftRuler s.1).length) (j : Fin segs.length) :
    (levelTables (inverse,tally n,xs,(segs.reverse.map Prod.snd).flatten))[j.val]'(by
      simp only [levelTables, levelBlocks_eq xs n hn, ← nodes, batchTables_correct _ _ _ width,
        List.length_map]
      exact j.isLt) = nodeTables (inverse,segs[j.val].1.1,segs[j.val].1.2,segs[j.val].2) := by
  simp only [levelTables, levelBlocks_eq xs n hn, ← nodes, batchTables_correct _ _ _ width,
    List.getElem_map]

/-- The full level query, including its generated tables, is an actual stack
task of polynomial cost in address width. The budget is uniform over valid
boxes, depths, address bits, and the choice of forward or inverse routing. -/
theorem levelTables_budget {ι : Type*} (k depth : ι → ℕ) (box : ι → List (ℕ × ℕ))
    (bits : ι → List Bool) (inverse : ι → Bool) (hk : ∀ i, 1 < k i)
    (hb : ∀ i, BoxShape.Valid (k i) (BoxScale.width (k i)) (box i))
    (hd : ∀ i, depth i ≤ k i) (ht : ∀ i, (bits i).length ≤ k i) :
    let q := fun i => (inverse i,tally (depth i),(box i).map (fun p => (tally p.1,tally p.2)),bits i)
    Task.BT k (fun i => send (q i)) (fun i => send (levelTables (q i))) := by
  dsimp only
  apply levelTables_poly.on
  have h := validBoxQuery_dom k box bits hk hb ht
  apply (h.add (((Dom.const k 2).mul (Dom.base k)).add (Dom.const k 4))).mono
  intro i
  simp only [size_prod, size_bit, size_tally, tally_length]
  specialize hd i
  omega

end CRTTable

end NearSquareRoot
end Computability
end OAI
