import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Basic

/-! # Evaluating the tail transpositions of an involution -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.TailTable

/-- A list of representatives of distinct two-point orbits acts by the
involution precisely on the union of the represented orbits. -/
theorem tailSwaps_fold {α : Type*} [DecidableEq α] (p : Equiv.Perm α)
    (hp : Function.Involutive p) (l : List α) (hn : l.Nodup)
    (h : ∀ i ∈ l, p i ∉ l) (x : α) :
    l.foldl (fun y i => Equiv.swap i (p i) y) x =
      if x ∈ l ∨ p x ∈ l then p x else x := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.nodup_cons.mp hn
    have hpa : p a ∉ l := fun hm => h a List.mem_cons_self (List.mem_cons_of_mem _ hm)
    have rest : ∀ i ∈ l, p i ∉ l := fun i hm hi =>
      h i (List.mem_cons_of_mem _ hm) (List.mem_cons_of_mem _ hi)
    rw [List.foldl_cons, ih hl rest]
    by_cases hx : x = a
    · subst x
      simp [hp a,ha,hpa]
    by_cases hpx : x = p a
    · subst x
      simp [hp a,ha,hpa]
    have hxa : p x ≠ a := fun eq => hpx ((hp x).symm.trans (congrArg p eq))
    simp [Equiv.swap_apply_of_ne_of_ne hx hpx,hx,hxa]

end Controlled.TailTable

end NearSquareRoot
end Computability
end OAI
