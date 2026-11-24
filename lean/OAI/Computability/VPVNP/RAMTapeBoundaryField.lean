import OAI.Computability.VPVNP.RAMTapeStackLift
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum

/-!
# Scanning one field of adjacent boundary records

A unary stack determines the field width. The control reads one pair of bits
per mark, saves the right bit, and moves the mark to a second stack. On reaching
the end of the width stack, it restores all marks for the next field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Boundary.Field

/-- Ports for two field streams, the unary width and its temporary copy, and saved right-hand
bits. -/
inductive Port where
  | width | widthBack | left | right | saved
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Construct the field-scanner bank from the width, restoration, input, and saved-bit stacks. -/
def store (width widthBack left right saved : List Bool) : Stacks Port
  | .width => width
  | .widthBack => widthBack
  | .left => left
  | .right => right
  | .saved => saved

/-- Field-scanning control carrying a comparison accumulator through paired reads, bit saving,
and width restoration. -/
inductive State (F : Type*) where
  | tick (f : F)
  | readLeft (f : F)
  | readRight (f : F) (a : Bool)
  | save (f : F) (b : Bool)
  | mark (f : F)
  | rewindWidth (f : F)
  | restoreMark (f : F)
  | done (f : F)
  | reject
  deriving DecidableEq, Fintype

variable {F : Type*} (step : F → Bool → Bool → F)

/-- Consume one bit pair per width mark, apply the comparison update, save the right bit, and
restore the width for the next field. -/
def code : StackCode Port (State F)
  | .tick f => .pop .width fun x => x.elim (.rewindWidth f) fun _ => .readLeft f
  | .readLeft f => .pop .left fun x => x.elim .reject (.readRight f)
  | .readRight f a => .pop .right fun x => x.elim .reject fun b => .save (step f a b) b
  | .save f b => .push .saved b (.mark f)
  | .mark f => .push .widthBack true (.tick f)
  | .rewindWidth f => .pop .widthBack fun x => x.elim (.done f) fun _ => .restoreMark f
  | .restoreMark f => .push .width true (.rewindWidth f)
  | .done _ => .halt true
  | .reject => .halt false

/-- Apply the field comparison update to consecutive bit pairs until either list ends. -/
def fold : F → List Bool → List Bool → F
  | f, a :: xs, b :: ys => fold (step f a b) xs ys
  | f, _, _ => f

private theorem update_width (w v l r s u : List Bool) :
    Function.update (store w v l r s) .width u = store u v l r s := by
  funext p; cases p <;> rfl

private theorem update_back (w v l r s u : List Bool) :
    Function.update (store w v l r s) .widthBack u = store w u l r s := by
  funext p; cases p <;> rfl

private theorem update_left (w v l r s u : List Bool) :
    Function.update (store w v l r s) .left u = store w v u r s := by
  funext p; cases p <;> rfl

private theorem update_right (w v l r s u : List Bool) :
    Function.update (store w v l r s) .right u = store w v l u s := by
  funext p; cases p <;> rfl

private theorem update_saved (w v l r s u : List Bool) :
    Function.update (store w v l r s) .saved u = store w v l r u := by
  funext p; cases p <;> rfl

private theorem readPair (f : F) (a b : Bool) (w v l r s : List Bool) :
    StackRuns (code step) 5 (.tick f) (store (true :: w) v (a :: l) (b :: r) s)
      (.tick (step f a b)) (store w (true :: v) l r (b :: s)) := by
  refine .cons (.pop rfl) ?_
  simp only [store, List.head?_cons, List.tail_cons, Option.elim_some, update_width]
  refine .cons (.pop rfl) ?_
  simp only [store, List.head?_cons, List.tail_cons, Option.elim_some, update_left]
  refine .cons (.pop rfl) ?_
  simp only [store, List.head?_cons, List.tail_cons, Option.elim_some, update_right]
  refine .cons (.push rfl) ?_
  simp only [store, update_saved]
  refine .cons (.push rfl) ?_
  simp only [store, update_back]
  exact .nil ..

private theorem collect (f : F) (xs ys l r s : List Bool) (n : ℕ)
    (h : xs.length = ys.length) :
    StackRuns (code step) (5 * xs.length + 1) (.tick f)
      (store (List.replicate xs.length true) (List.replicate n true) (xs ++ l) (ys ++ r) s)
      (.rewindWidth (fold step f xs ys))
      (store [] (List.replicate (xs.length + n) true) l r (ys.reverse ++ s)) := by
  induction xs generalizing f ys n s with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp h.symm
    subst ys
    simp only [List.length_nil, List.replicate_zero, List.nil_append, Nat.zero_add, Nat.mul_zero,
      List.reverse_nil, fold]
    refine .cons (.pop rfl) ?_
    simp only [store, List.head?_nil, List.tail_nil, Option.elim_none, update_width]
    exact .nil ..
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      have h₁ := readPair step f a b (List.replicate xs.length true) (List.replicate n true)
        (xs ++ l) (ys ++ r) s
      have h₂ := ih (step f a b) ys (b :: s) (n+1) (Nat.succ.inj h)
      rw [List.replicate_succ (n := n)] at h₂
      simpa [List.replicate_succ, fold, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        List.reverse_cons, List.append_assoc] using h₁.trans h₂

private theorem rewind (f : F) (n : ℕ) (w l r s : List Bool) :
    StackRuns (code step) (2 * n + 1) (.rewindWidth f) (store w (List.replicate n true) l r s)
      (.done f) (store (List.replicate n true ++ w) [] l r s) := by
  induction n generalizing w with
  | zero =>
    refine .cons (.pop rfl) ?_
    simp only [store, List.replicate_zero, List.head?_nil, List.tail_nil, Option.elim_none, update_back,
      List.nil_append]
    exact .nil ..
  | succ n ih =>
    have hh : 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 := by omega
    rw [hh, List.replicate_succ]
    refine .cons (.pop rfl) ?_
    simp only [store, List.head?_cons, List.tail_cons, Option.elim_some, update_back]
    refine .cons (.push rfl) ?_
    simp only [store, update_width]
    have hr := ih (true :: w)
    rw [← List.singleton_append (x := true), ← List.append_assoc, ← List.replicate_succ'] at hr
    exact hr

/-- A field of width `xs.length` takes five instructions per pair and two per
restored mark. The two additional pops detect the ends of the width stacks. -/
theorem runs (f : F) (xs ys leftTail rightTail saved : List Bool) (h : xs.length = ys.length) :
    StackRuns (code step) (7 * xs.length + 2) (.tick f)
      (store (List.replicate xs.length true) [] (xs ++ leftTail) (ys ++ rightTail) saved)
      (.done (fold step f xs ys))
      (store (List.replicate xs.length true) [] leftTail rightTail (ys.reverse ++ saved)) := by
  have h₁ := collect step f xs ys leftTail rightTail saved 0 h
  have h₂ := rewind step (fold step f xs ys) xs.length [] leftTail rightTail (ys.reverse ++ saved)
  simp only [List.replicate_zero, Nat.add_zero] at h₁
  simp only [List.append_nil] at h₂
  exact (show 5 * xs.length + 1 + (2 * xs.length + 1) = 7 * xs.length + 2 by omega) ▸ h₁.trans h₂

end RAMTape.Boundary.Field

end VPVNP
end Computability
end OAI
