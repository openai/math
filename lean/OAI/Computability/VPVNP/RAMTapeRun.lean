import OAI.Computability.VPVNP.RAMTape

/-!
# Deterministic routines inside a branching tape program

A run contains only one-record rows. Executing it consumes its recorded number
of transitions and preserves the multiplicity of all continuations.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape

open UniversalMachine Turing

variable {Q : Type*}

/-- An exact finite run of deterministic two-tape commands between named configurations. -/
inductive Runs (code : Control Q) :
    ℕ → Q → Tape Symbol → Tape Symbol → Q → Tape Symbol → Tape Symbol → Prop
  | nil (q t u) : Runs code 0 q t u q t u
  | cons {q t u q' a d b e n r x y}
      (h : code q t.head u.head = .one (.next q' a d b e))
      (tail : Runs code n q' (updateTape t a d) (updateTape u b e) r x y) :
      Runs code (n+1) q t u r x y

theorem Runs.single {code : Control Q} {q t u q' a d b e}
    (h : code q t.head u.head = .one (.next q' a d b e)) :
    Runs code 1 q t u q' (updateTape t a d) (updateTape u b e) :=
  .cons h (.nil ..)

theorem Runs.trans {code : Control Q} {a b q t u q' x y r x' y'}
    (h : Runs code a q t u q' x y) (g : Runs code b q' x y r x' y') :
    Runs code (a+b) q t u r x' y' := by
  induction h with
  | nil => simpa using g
  | cons hs _ ih => simpa [Nat.succ_add] using Runs.cons hs (ih g)

theorem Runs.count [Fintype Q] {code : Control Q} {n q t u q' x y}
    (h : Runs code n q t u q' x y) (start : Q) (fuel : ℕ) :
    RAMTape.count start code (fuel+n) q t u = RAMTape.count start code fuel q' x y := by
  induction h with
  | nil => rfl
  | cons hs _ ih => rw [Nat.add_succ, paths_step, hs]; exact ih

/-- A two-way tape specified by the cells to the left and at or to the right of the head. -/
abbrev cells := Tape.mk₂ (Γ := Symbol)

@[simp] theorem cells_head (l : List Symbol) (x : Symbol) (r : List Symbol) :
    (cells l (x :: r)).head = x := rfl

@[simp] theorem cells_head_nil (l : List Symbol) : (cells l []).head = 0 := rfl

@[simp] theorem update_stay (t : Tape Symbol) : updateTape t t.head 0 = t := Tape.write_self t

theorem update_right (l r : List Symbol) (x y : Symbol) :
    updateTape (cells l (x :: r)) y 2 = cells (y :: l) r := rfl

theorem update_left (l r : List Symbol) (x z y : Symbol) :
    updateTape (cells (z :: l) (x :: r)) y 1 = cells l (z :: y :: r) := rfl

theorem cells_nil_cons_blank (l r : List Symbol) :
    cells l (r ++ [0]) = cells l r := by
  have he : ListBlank.mk (r ++ [(0 : Symbol)]) = ListBlank.mk r :=
    Quotient.sound (Or.inr ⟨1, rfl⟩)
  exact congrArg (Tape.mk' (ListBlank.mk l)) he

/-- The head points to the stack top and every cell on its left is blank. -/
abbrev tapeList (s : List Symbol) := cells [] s

theorem cells_blank_left (s : List Symbol) : cells [0] s = tapeList s :=
  congrArg (fun l => Tape.mk' l (ListBlank.mk s))
    (show ListBlank.mk [(0 : Symbol)] = ListBlank.mk [] from Quotient.sound (Or.inr ⟨1, rfl⟩))

@[simp] theorem pop_cell (a : Symbol) (s : List Symbol) :
    updateTape (tapeList (a :: s)) 0 2 = tapeList s := cells_blank_left s

theorem left_for_push (s : List Symbol) :
    updateTape (tapeList s) (tapeList s).head 1 = tapeList (0 :: s) := by
  change ((tapeList s).write (tapeList s).head).move .left = _
  rw [Tape.write_self]
  change (Tape.mk' (ListBlank.mk []) (ListBlank.mk s)).move .left = _
  rw [Tape.move_left_mk']
  rfl

@[simp] theorem replace_top (a x : Symbol) (s : List Symbol) :
    updateTape (tapeList (x :: s)) a 0 = tapeList (a :: s) := rfl

@[simp] theorem write_left (a x : Symbol) (s : List Symbol) :
    updateTape (tapeList (x :: s)) a 1 = tapeList (0 :: a :: s) := rfl

end RAMTape

end VPVNP
end Computability
end OAI
