import OAI.Computability.VPVNP.RAMTapeRun

/-!
# Signed head displacement in a two-tape routine

Positions on each bidirectional tape are measured from its initial head.
The same transition that writes the symbol and moves the tape contributes
one signed unit, or zero for a stationary head.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape

open UniversalMachine Turing

/-- Directions 0, 1 and 2 in a table row mean stay, left and right. -/
def moveDelta (d : Fin 3) : ℤ := if d = 0 then 0 else if d = 1 then -1 else 1

@[simp] theorem delta_stay : moveDelta 0 = 0 := rfl
@[simp] theorem delta_left : moveDelta 1 = -1 := rfl
@[simp] theorem delta_right : moveDelta 2 = 1 := rfl

theorem delta_range (d : Fin 3) : -1 ≤ moveDelta d ∧ moveDelta d ≤ 1 := by
  simp only [moveDelta]
  split <;> first | decide | split <;> decide

variable {Q : Type*}

/-- A deterministic physical run with the two net head displacements. -/
inductive Travel (code : Control Q) :
    ℕ → ℤ → ℤ → Q → Tape Symbol → Tape Symbol → Q → Tape Symbol → Tape Symbol → Prop
  | nil (q t u) : Travel code 0 0 0 q t u q t u
  | cons {q t u q' a d b e n dx dy r x y}
      (h : code q t.head u.head = .one (.next q' a d b e))
      (tail : Travel code n dx dy q' (updateTape t a d) (updateTape u b e) r x y) :
      Travel code (n+1) (moveDelta d + dx) (moveDelta e + dy) q t u r x y

theorem Travel.single {code : Control Q} {q t u q' a d b e}
    (h : code q t.head u.head = .one (.next q' a d b e)) :
    Travel code 1 (moveDelta d) (moveDelta e) q t u q' (updateTape t a d) (updateTape u b e) := by
  simpa using Travel.cons h (.nil ..)

theorem Travel.trans {code : Control Q} {a b dx dy ex ey q t u q' x y r x' y'}
    (h : Travel code a dx dy q t u q' x y) (g : Travel code b ex ey q' x y r x' y') :
    Travel code (a+b) (dx+ex) (dy+ey) q t u r x' y' := by
  induction h with
  | nil => simpa using g
  | cons hs _ ih => simpa [Nat.succ_add, Int.add_assoc] using Travel.cons hs (ih g)

theorem Travel.runs {code : Control Q} {n dx dy q t u r x y}
    (h : Travel code n dx dy q t u r x y) : Runs code n q t u r x y := by
  induction h with
  | nil => exact .nil ..
  | cons hs _ ih => exact .cons hs ih

end RAMTape

end VPVNP
end Computability
end OAI
