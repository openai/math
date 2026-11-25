import OAI.Computability.NearSquareRoot.CRTTableInput

/-! # Slicing the controls of one CRT routing level

All bits of a control setting arrive in one MSF word. Each node of a
balanced level consumes the contiguous fields for its own left child.
We scan the nodes in decreasing axis order and accumulate the outputs in
increasing order. One node table program can therefore be used at every
node of the level, including levels with unequal child counts.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable
open IntegerMultiplication IntegerMultiplication.Code

abbrev LevelBlock := List ControlAxis × List ControlAxis
abbrev LevelInput := Bool × List LevelBlock × List Bool
abbrev LocalControl := List ControlAxis × List ControlAxis × List Bool
private abbrev SliceState := List Bool × List LocalControl

/-- Unary ruler for the number of bits supplied by the left child. -/
def leftRuler (b : LevelBlock) : Tally := (b.1.map Prod.fst).flatten

private theorem leftRuler_easy : Easy leftRuler := by
  unfold leftRuler
  fun_prop

@[simp] theorem leftRuler_length (b : LevelBlock) :
    (leftRuler b).length = (b.1.map (fun a => a.1.length)).sum := by
  simp [leftRuler, List.length_flatten, List.map_map, Function.comp_def]

private def sliceStep (p : SliceState × LevelBlock) : SliceState :=
  let seg := cutLists (leftRuler p.2, p.1.1)
  (seg.2, (p.2.1, p.2.2, seg.1) :: p.1.2)

private theorem sliceStep_easy : Easy sliceStep := by
  have hc := easy_cut (g := fun p : SliceState × LevelBlock => (leftRuler p.2, p.1.1))
    ((Easy.snd.compose leftRuler_easy).pair (by fun_prop))
  exact hc.sndCompose.pair
    ((((show Easy (fun p : SliceState × LevelBlock => p.2.1) by fun_prop).pair
      ((show Easy (fun p : SliceState × LevelBlock => p.2.2) by fun_prop).pair hc.fstCompose)).pair
      (by fun_prop)).compose Easy.cons)

private theorem sliceStep_size (s : SliceState) (b : LevelBlock) :
    size (sliceStep (s,b)) ≤ size s + 4 * size b := by
  simp only [sliceStep, cutLists, size_prod, size_cons, Bits.size_word, List.length_take,
    List.length_drop]
  have := size_pos b.1
  have := size_pos b.2
  omega

private theorem sliceFold_poly :
    Poly (fun i : List LevelBlock × SliceState =>
      i.1.foldl (fun s b => sliceStep (s,b)) i.2) := by
  apply Poly.fold_left sliceStep_easy.poly 4 1
  intro i l h
  have bound (s : SliceState) (bs : List LevelBlock) :
      size (bs.foldl (fun s b => sliceStep (s,b)) s) ≤ size s + 4 * size bs := by
    induction bs generalizing s with
    | nil => simp
    | cons b bs ih =>
      simp only [List.foldl_cons, size_cons]
      exact (ih _).trans (by have := sliceStep_size s b; omega)
  have hp := bound i.2 l
  obtain ⟨r,hr⟩ := h
  have hs := size_append_right l r
  rw [hr] at hs
  have hn := size_pos r
  change _ ≤ 4 * ((size i.1 + size i.2 + 1) + 1)^1
  simp only [pow_one]
  omega

/-- Supply the local control word to each node in increasing axis order. -/
def splitNodes (p : List LevelBlock × List Bool) : List LocalControl :=
  (p.1.reverse.foldl (fun s b => sliceStep (s,b)) (p.2, [])).2

theorem splitNodes_poly : Poly splitNodes := by
  exact ((show Poly (fun p : List LevelBlock × List Bool =>
    (p.1.reverse, p.2, ([] : List LocalControl))) by fun_prop).compose sliceFold_poly).sndCompose

private theorem sliceFold_correct (segs : List (LevelBlock × List Bool))
    (width : ∀ s ∈ segs, s.2.length = (leftRuler s.1).length)
    (tail : List Bool) (saved : List LocalControl) :
    (segs.map Prod.fst).foldl (fun s b => sliceStep (s,b)) ((segs.map Prod.snd).flatten ++ tail,saved) =
      (tail,(segs.map (fun s => (s.1.1, s.1.2, s.2))).reverse ++ saved) := by
  induction segs generalizing saved with
  | nil => simp
  | cons s segs ih =>
    have hw := width s (by simp)
    have ht := ih (fun z hz => width z (by simp [hz]))
    have hstep : sliceStep ((s.2 ++ ((segs.map Prod.snd).flatten ++ tail), saved), s.1) =
        ((segs.map Prod.snd).flatten ++ tail, (s.1.1,s.1.2,s.2)::saved) := by
      simp [sliceStep, cutLists, ← hw]
    simp only [List.map_cons, List.flatten_cons, List.append_assoc, List.foldl_cons,
      hstep, ht, List.reverse_cons, List.singleton_append]

theorem splitNodes_correct (segs : List (LevelBlock × List Bool))
    (width : ∀ s ∈ segs, s.2.length = (leftRuler s.1).length) :
    splitNodes (segs.map Prod.fst, (segs.reverse.map Prod.snd).flatten) =
      segs.map (fun s => (s.1.1,s.1.2,s.2)) := by
  have h := congrArg Prod.snd (sliceFold_correct segs.reverse
    (fun s hs => width s (by simpa using hs)) [] [])
  simpa [splitNodes] using h

/-- Run the same table constructor at every node with its own slice. -/
def batchTables {Y : Type} (f : (Bool × LocalControl) → Y) (i : LevelInput) : List Y :=
  polyPush f (i.1,splitNodes i.2)

theorem batchTables_poly {Y : Type} [Codec Y] {f : (Bool × LocalControl) → Y} (h : Poly f) :
    Poly (batchTables f) :=
  ((show Poly (fun i : LevelInput => i.1) by fun_prop).pair
    ((show Poly (fun i : LevelInput => i.2) by fun_prop).compose splitNodes_poly)).compose
      (Poly.push false ([],[],[]) h)

theorem batchTables_correct {Y : Type} (f : (Bool × LocalControl) → Y) (inverse : Bool)
    (segs : List (LevelBlock × List Bool))
    (width : ∀ s ∈ segs, s.2.length = (leftRuler s.1).length) :
    batchTables f (inverse,segs.map Prod.fst,(segs.reverse.map Prod.snd).flatten) =
      segs.map (fun s => f (inverse,s.1.1,s.1.2,s.2)) := by
  simp only [batchTables, polyPush, splitNodes_correct _ width, List.map_map, Function.comp_def]

theorem batchTables_getElem {Y : Type} (f : (Bool × LocalControl) → Y) (inverse : Bool)
    (segs : List (LevelBlock × List Bool))
    (width : ∀ s ∈ segs, s.2.length = (leftRuler s.1).length) (j : Fin segs.length) :
    (batchTables f (inverse,segs.map Prod.fst,(segs.reverse.map Prod.snd).flatten))[j.val]'(by
      rw [batchTables_correct _ _ _ width]
      simp) = f (inverse,segs[j.val].1.1,segs[j.val].1.2,segs[j.val].2) := by
  simp only [batchTables_correct _ _ _ width, List.getElem_map]

end CRTTable

end NearSquareRoot
end Computability
end OAI
