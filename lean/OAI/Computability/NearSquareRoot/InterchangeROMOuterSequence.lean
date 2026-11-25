import OAI.Computability.NearSquareRoot.InterchangeROMRecursionOpen
import OAI.Computability.NearSquareRoot.InterchangeROMRoute
import OAI.Computability.NearSquareRoot.BoundedProductRight

/-! # Composition of native stages under one literal recursive binder -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRecursion
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Loom
  NearSquareRoot.Space NearSquareRoot.InterchangeSpace NearSquareRoot.InterchangeROM

variable {X : Type} {job : Job X} {parent c d : Cmd} {s f s' f' : List X}
    {u v z : Tree} {w w' p p' r r' : ℕ}

private theorem peak_append (g : X → ℕ) (xs ys : List X) :
    childPeak g (xs ++ ys) = max (childPeak g xs) (childPeak g ys) := by
  induction xs with
  | nil => simp [childPeak]
  | cons x xs ih => change max (g x) (childPeak g (xs ++ ys)) = max (max (g x) (childPeak g xs)) _
                    rw [ih,max_assoc]

/-- Each concrete call is charged once. A join adds a pending return only
during its first component; the small and full ledgers stay distinct. -/
theorem At.sequence (one : At parent c job s f u v w p r)
    (two : At parent d job s' f' v z w' p' r') :
    At parent (c.join d) job (s++s') (f++f') u z (w+w'+2) (max p p') (max (r+1) r') := by
  intro env t a k children deck base live
  have first := one env t a k (fun y hy => children y (by simpa only [List.mem_append] using
    (show (y ∈ s ∨ y ∈ s') ∨ y ∈ f ∨ y ∈ f' from
      (List.mem_append.mp hy).elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inr (Or.inl h))))) deck base live
  have second := two env t a k (fun y hy => children y (by simpa only [List.mem_append] using
    (show (y ∈ s ∨ y ∈ s') ∨ y ∈ f ∨ y ∈ f' from
      (List.mem_append.mp hy).elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h))))) deck base live
  simp only [peak_append,List.map_append,List.sum_append] at first second ⊢
  let cap := base+max (w+w'+2+max (childPeak a s) (childPeak a s'))
    (max p p'+max (childPeak a f) (childPeak a f'))
  let depth := max (w+w'+2+max (childPeak k s) (childPeak k s'))
    (max (r+1) r'+max (childPeak k f) (childPeak k f'))
  have left := first.mono le_rfl (show _ ≤ cap by dsimp [cap]; omega) le_rfl
  have right := second.mono le_rfl (show _ ≤ cap by dsimp [cap]; omega)
    (show _ ≤ depth by dsimp [depth]; omega)
  exact (left.join right (by dsimp [depth]; omega)).mono (by omega) le_rfl le_rfl

/-- A local frame-generating step returns before any child. -/
theorem At.local_run (h : ∀ env deck base, DeckCap base deck →
      BoundedFits (parent::env) c (pile 0 u deck) (pile 0 v deck) w (base+w) w) :
    At parent c job [] [] u v w 0 0 := by
  intro env t a k _ deck base live
  simpa only [List.nil_append,List.map_nil,List.sum_nil,childPeak,List.foldr_nil,
    Nat.add_zero,Nat.zero_add,Nat.max_zero] using h env deck base live

/-- The local time bound alone supplies a stack bound for a pass containing
no recursive calls. -/
theorem At.local_fits (h : ∀ env deck, Fits (parent::env) c (pile 0 u deck) (pile 0 v deck) w) :
    At parent c job [] [] u v (w+u.count) 0 0 := by
  apply At.local_run
  intro env deck base hd
  apply (BoundedFits.of_fits (h env deck) (cap:=base+(w+u.count)) (depth:=w+u.count)
    (fun j => by have := (hd.pile 0 u) j; omega) (by omega)).mono (by omega) le_rfl le_rfl

/-- A header may be parked around a small-only stage. The child time retains
unit coefficient even when it greatly exceeds the space used by the row bank. -/
theorem At.under_header (h : At parent c job s [] u v w 0 0) (tag : Tree) :
    At parent (underHeader c) job s [] (.fork tag u) (.fork tag v) (w+100*(tag.count+1)) 0 0 := by
  intro env t a k call deck base live
  have sub := h env t a k call (pile 1 tag deck) (base+tag.count) (live.pile 1 tag)
  simp only [List.append_nil,childPeak,List.foldr_nil,Nat.add_zero,Nat.max_zero] at sub ⊢
  let S := (s.foldr (fun q m => max (a q) m) 0)
  let D := (s.foldr (fun q m => max (k q) m) 0)
  let cap := base+(w+100*(tag.count+1)+S)
  let depth := w+100*(tag.count+1)+D
  let startBudget := base+tag.count+(w+S)
  change BoundedFits _ _ _ _ _ startBudget (w+D) at sub
  have start : DeckCap startBudget (pile 0 u (pile 1 tag deck)) := sub.choose_spec.2.start
  have finish : DeckCap startBudget (pile 0 v (pile 1 tag deck)) := sub.choose_spec.2.finish
  rw [pile_comm 0 _ deck 1 _ (by decide)] at start finish
  have input := start.unpile.pile 0 tag
  have output := finish.unpile.pile 0 tag
  have room : startBudget+tag.count+42*tag.count+1 ≤ cap := by dsimp [startBudget,cap]; omega
  have rmove : 42*tag.count+1 ≤ depth := by dsimp [depth]; omega
  have hr : w+D+1 ≤ depth := by dsimp [depth]; omega
  have toWork := BoundedFits.move (i:=0) (j:=1) (u:=2) (by decide) (by decide) tag (parent::env)
    (pile 0 u deck) input (cap:=cap) (by omega) (depth:=42*tag.count) le_rfl
  have restore := BoundedFits.move (i:=1) (j:=0) (u:=2) (by decide) (by decide) tag (parent::env)
    (pile 0 v deck) finish (cap:=cap) (by omega) (depth:=42*tag.count) le_rfl
  rw [pile_comm 1 _ deck 0 _ (by decide)] at toWork restore
  have packRun := BoundedFits.pack tag v deck 0 (parent::env) (depth:=depth)
    (output.coverFork.mono (by omega : _ ≤ cap))
  have middle := sub.mono le_rfl (by omega : startBudget ≤ cap) le_rfl
  have joined := toWork.join (middle.join (restore.join packRun rmove) hr) rmove
  exact (BoundedFits.pair (c:=fun _ => .pass) joined (input.coverFork.mono (by omega))
    (by omega)).mono (by omega) le_rfl le_rfl

end InterchangeROMRecursion

end NearSquareRoot
end Computability
end OAI
