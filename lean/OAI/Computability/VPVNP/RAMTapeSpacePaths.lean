import OAI.Computability.VPVNP.RAMTapeSpaceTravel

/-!
# Head positions along a branching physical execution

A path can follow either occupied continuation slot. Its integer indices
measure the total displacement on each tape; applying the displacement bound
to every prefix bounds every cell visited.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape

open UniversalMachine Turing

variable {Q : Type*}

/-- A command occupies one of the available continuation slots in a physical machine step. -/
def Choices.contains (branches : Choices Q) (cmd : Command Q) : Prop :=
  match branches with
  | .stop => False
  | .one a => a = cmd
  | .two a b => a = cmd ∨ b = cmd

/-- A prefix following actual continuing commands, with its physical
head displacement on both tapes. -/
inductive HeadPath (code : Control Q) :
    ℕ → ℤ → ℤ → Q → Tape Symbol → Tape Symbol → Q → Tape Symbol → Tape Symbol → Prop
  | nil (q t u) : HeadPath code 0 0 0 q t u q t u
  | cons {q t u q' a d b e n dx dy r x y}
      (h : (code q t.head u.head).contains (.next q' a d b e))
      (tail : HeadPath code n dx dy q' (updateTape t a d) (updateTape u b e) r x y) :
      HeadPath code (n+1) (moveDelta d + dx) (moveDelta e + dy) q t u r x y

/-- Each instruction moves each head by at most one cell. -/
theorem HeadPath.range {code : Control Q} {n dx dy q t u r x y}
    (p : HeadPath code n dx dy q t u r x y) :
    -(n : ℤ) ≤ dx ∧ dx ≤ n ∧ -(n : ℤ) ≤ dy ∧ dy ≤ n := by
  induction p with
  | nil => simp
  | @cons _ _ _ _ _ d _ e _ _ _ _ _ _ _ _ ih =>
    have := delta_range d
    have := delta_range e
    push_cast
    omega

/-- An execution that runs at least as long as a deterministic routine
must follow that routine, leaving only its suffix and residual displacement. -/
theorem Travel.suffix {code : Control Q} {m dx dy q t u r x y}
    (run : Travel code m dx dy q t u r x y) {n ex ey v a b}
    (walk : HeadPath code n ex ey q t u v a b) (hlen : m ≤ n) :
    ∃ k wx wy, n = m + k ∧ ex = dx + wx ∧ ey = dy + wy ∧ HeadPath code k wx wy r x y v a b := by
  induction run generalizing n ex ey with
  | nil => exact ⟨n, ex, ey, by omega, by omega, by omega, walk⟩
  | cons hr _ ih =>
    cases walk with
    | nil => omega
    | cons hw tail =>
      rw [hr] at hw
      simp only [Choices.contains] at hw
      cases hw
      obtain ⟨k, wx, wy, hk, hx, hy, hs⟩ := ih tail (by omega)
      exact ⟨k, wx, wy, by omega, by omega, by omega, hs⟩

end RAMTape

end VPVNP
end Computability
end OAI
