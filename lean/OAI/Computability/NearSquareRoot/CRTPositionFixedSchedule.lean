import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

/-! # Fixed schedule for the six unordered pairs of three chunks

The endpoints of a transposition can be tagged by any assignment to three
chunks. Exactly one of the six stages owns the unordered pair of tags, including
when the endpoints lie in the same chunk.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.FixedSchedule

variable {α : Type*} (u : Equiv.Perm α) (hu : Function.Involutive u) (tag : α → Fin 3)

def pairs : List (Fin 3 × Fin 3) := [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)]

private def test (c d : Fin 3) (x : α) : Prop :=
  (tag x = c ∧ tag (u x) = d) ∨ (tag x = d ∧ tag (u x) = c)

private instance (c d : Fin 3) (x : α) : Decidable (test u tag c d x) := by
  unfold test
  infer_instance

private def select (c d : Fin 3) (x : α) : α := if test u tag c d x then u x else x

include hu
private theorem stable (c d : Fin 3) (x : α) : test u tag c d (u x) ↔ test u tag c d x := by
  unfold test
  rw [hu x]
  tauto

private theorem select_involutive (c d : Fin 3) : Function.Involutive (select u tag c d) := by
  intro x
  by_cases t : test u tag c d x <;> simp [select,t,stable u hu tag,hu x]

/-- Restriction of an involution to the transpositions with the indicated pair
of chunk endpoints. Either orientation of the two chunks is accepted. -/
def restrict (c d : Fin 3) : Equiv.Perm α :=
  ⟨select u tag c d,select u tag c d,select_involutive u hu tag c d,select_involutive u hu tag c d⟩

theorem restrict_apply (c d : Fin 3) (x : α) :
    restrict u hu tag c d x = if (tag x = c ∧ tag (u x) = d) ∨ (tag x = d ∧ tag (u x) = c)
      then u x else x := rfl

theorem restrict_involutive (c d : Fin 3) : Function.Involutive (restrict u hu tag c d) :=
  select_involutive u hu tag c d

/-- The fixed six-pair schedule realizes the original involution. -/
theorem run (x : α) :
    pairs.foldl (fun y q => restrict u hu tag q.1 q.2 y) x = u x := by
  have action (a b : Fin 3) (ha : tag x = a) (hb : tag (u x) = b) :
      pairs.foldl (fun y q => restrict u hu tag q.1 q.2 y) x = u x := by
    fin_cases a <;> fin_cases b <;> simp [pairs,restrict_apply,hu x,ha,hb]
  exact action _ _ rfl rfl

/-- Applying the six chunk-pair programs in the listed order transforms
every stored word by pullback along the original position permutation. -/
theorem word_action {V : Type*} (w : α → V) :
    pairs.foldl (fun word q => word ∘ restrict u hu tag q.1 q.2) w = w ∘ u := by
  have forward (l : List (Fin 3 × Fin 3)) (v : α → V) (x : α) :
      l.foldl (fun word q => word ∘ restrict u hu tag q.1 q.2) v
        (l.foldl (fun y q => restrict u hu tag q.1 q.2 y) x) = v x := by
    induction l generalizing x v with
    | nil => rfl
    | cons a l ih =>
      simp only [List.foldl_cons,ih,Function.comp_apply,restrict_involutive u hu tag a.1 a.2 x]
  funext x
  have action := forward pairs w (u x)
  rw [run,hu x] at action
  exact action

end Controlled.FixedSchedule

end NearSquareRoot
end Computability
end OAI
