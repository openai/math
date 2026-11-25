import OAI.Computability.MultitapeWeakETH.SparseLeafProgram
import OAI.Computability.MultitapeWeakETH.SparsePreparation
import OAI.Computability.MultitapeWeakETH.Sparsification

/-! # The finite-cost disjoint worklist on sparse counting tapes -/

namespace OAI.Computability.MultitapeWeakETH.SparseIteration

open IntegerMultiplication Code Bits Strip
open Algorithms.SubexponentialSAT SqrtLogSpace.DisjointReuse SparseDFSRefinement
open private data? data_poly present present_poly from OAI.Computability.MultitapeWeakETH.WitnessWalk
open scoped Classical
noncomputable section

abbrev Work := List Word × Bool
abbrev Param := ((Tally × Tally) × Tally) × Word
-- The fields are volume, variable count, search allowance, and threshold.
abbrev Input := (Param × Tally) × Work

private def front (xs : List Word) := xs.headD []
private theorem front_poly : Poly front := by
  convert (Easy.listCase (X:=Word) [] Easy.fst).poly using 1
  funext xs; cases xs <;> rfl

private theorem tail_poly : Poly (List.tail (α:=Word)) := by
  convert (Easy.listCase (X:=Word) [] Easy.snd).poly using 1
  funext xs; cases xs <;> rfl

private theorem empty_poly : Poly (List.isEmpty (α:=Word)) := by
  convert (Easy.listCase (X:=Word) true (Easy.const false)).poly using 1
  funext xs; cases xs <;> rfl

private def clipped (cap : Tally) (w : Word) := (cutLists (cap,w)).1

private def prepend (q : (Tally × List Word) × List Word) : List Word :=
  clipped q.1.1 (front q.1.2) :: clipped q.1.1 (front q.1.2.tail) :: q.2

private theorem prepend_poly : Poly prepend := by
  have cap : Poly (fun q : (Tally × List Word) × List Word => q.1.1) := by fun_prop
  have rows : Poly (fun q : (Tally × List Word) × List Word => q.1.2) := by fun_prop
  have cut : Poly (fun q : Tally × Word => clipped q.1 q.2) := (easy_cut Easy.identity).poly.fstCompose
  have a := (cap.pair (rows.compose front_poly)).compose cut
  have b := (cap.pair ((rows.compose tail_poly).compose front_poly)).compose cut
  exact (a.pair ((b.pair Easy.snd.poly).compose Easy.cons.poly)).compose Easy.cons.poly

private def positive (w : Word) := !(w.filter id).isEmpty

private theorem positive_poly : Poly positive := by
  have empty : Poly (List.isEmpty (α:=Bool)) := by
    convert (Easy.listCase (X:=Bool) true (Easy.const false)).poly using 1
    funext xs; cases xs <;> rfl
  exact ((Poly.filter id (Poly.identity (X:=Bool))).compose empty).compose Iter.negate.poly

private theorem positive_eq (w : Word) : positive w = decide (0 < value w) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;> simp [positive,value_cons,digit] at ih ⊢
    omega

variable (split : Word × Word → Option (List Word)) (leaf : NativeGrid.CountQuery → Word)

private def test (q : Input) := split (q.1.1.2,front q.2.1)
private def answer (q : Input) := positive (leaf ((q.1.1.1.1.1,q.1.1.1.1.2,front q.2.1),q.1.1.1.2))

def visit (q : Input) : Work :=
  bif q.2.1.isEmpty then q.2 else
    bif present (test split q) then
      (prepend ((q.1.2,data? (test split q)),q.2.1.tail),q.2.2)
    else (q.2.1.tail,q.2.2 || answer leaf q)

theorem visit_poly (ps : Poly split) (pl : Poly leaf) : Poly (visit split leaf) := by
  have rows : Poly (fun q : Input => q.2.1) := by fun_prop
  have w := rows.compose front_poly
  have sel : Poly (test split) := ((show Poly (fun q : Input => q.1.1.2) by fun_prop).pair w).compose ps
  have args := ((show Poly (fun q : Input => q.1.1.1.1.1) by fun_prop).pair
    ((show Poly (fun q : Input => q.1.1.1.1.2) by fun_prop).pair w)).pair
      (show Poly (fun q : Input => q.1.1.1.2) by fun_prop)
  have yes : Poly (answer leaf) := (args.compose pl).compose positive_poly
  have hit : Poly (fun q : Input => q.2.2) := by fun_prop
  have rest := rows.compose tail_poly
  have children := (((show Poly (fun q : Input => q.1.2) by fun_prop).pair (sel.compose data_poly)).pair rest).compose prepend_poly
  exact Poly.choose (rows.compose empty_poly) Easy.snd.poly (Poly.choose (sel.compose present_poly)
    (children.pair hit) (rest.pair ((hit.pair yes).compose (Easy.finite (fun p : Bool × Bool => p.1 || p.2)).poly)))

private theorem word_size (w : Word) : size w=2*w.length+1 := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [ih,Nat.mul_add]; omega

private theorem visit_size (c : Param × Tally) (w : Work) :
    size (visit split leaf (c,w)) ≤ 8*size c+size w := by
  rcases w with ⟨xs,b⟩
  cases xs with
  | nil => simp [visit]
  | cons x xs =>
    have bit (b : Bool) : size b=1 := rfl
    have cut (y : Word) : size (clipped c.2 y) ≤ 2*c.2.length+1 := by
      simp [clipped,cutLists,word_size]
    simp only [visit,List.isEmpty_cons,Bool.cond_false,List.tail_cons]
    cases hit : present (test split (c,x::xs,b)) with
    | true =>
      simp only [Bool.cond_true,prepend,size_prod,size_cons,size_tally,bit]
      have a := cut (front (data? (test split (c,x::xs,b))))
      have d := cut (front (data? (test split (c,x::xs,b))).tail)
      omega
    | false => simp [size_prod,bit]; omega

def execute (q : Tally × (Param × Tally) × Work) :=
  ((fun w => visit split leaf (q.2.1,w))^[q.1.length] q.2.2).2

theorem execute_poly (ps : Poly split) (pl : Poly leaf) : Poly (execute split leaf) :=
  (Poly.bounder _ (visit_poly split leaf ps pl) 8 (visit_size split leaf)).sndCompose

end
end OAI.Computability.MultitapeWeakETH.SparseIteration
