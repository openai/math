import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Replacing a column of a completion

When a fresh column extends an independent frame, it can take the place of
any of the completion columns. The original and the modified completions
together span exactly the completion with the fresh column adjoined.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

open Set Submodule

variable {K V ι : Type*} [Semiring K] [AddCommMonoid V] [Module K V] {s : ℕ}

/-- Discard the last column of an independent completed frame. -/
theorem independent_completion_init {v : ι → V} {w : Fin s → V} {x : V}
    (h : LinearIndependent K (Sum.elim v (Fin.snoc w x))) :
    LinearIndependent K (Sum.elim v w) := by
  have h' := h.comp (Sum.map id Fin.castSucc)
    (Function.injective_id.sumMap (Fin.castSucc_injective s))
  convert h' using 1
  funext a
  rcases a with a | j
  · rfl
  · simp

/-- Replace one completion column by the last column of an independent extension. -/
theorem independent_completion_replacement {v : ι → V} {w : Fin s → V} {x : V}
    (i : Fin s) (h : LinearIndependent K (Sum.elim v (Fin.snoc w x))) :
    LinearIndependent K (Sum.elim v (Function.update w i x)) := by
  let σ := Equiv.swap i.castSucc (Fin.last s)
  have h' := h.comp (Sum.map id (σ ∘ Fin.castSucc))
    (Function.injective_id.sumMap (σ.injective.comp (Fin.castSucc_injective s)))
  convert h' using 1
  funext a
  rcases a with a | j
  · rfl
  · change Function.update w i x j = Fin.snoc (α := fun _ ↦ V) w x (σ j.castSucc)
    by_cases hj : j = i
    · subst j
      simp [σ]
    · rw [Function.update_of_ne hj, Equiv.swap_apply_of_ne_of_ne
        ((Fin.castSucc_injective s).ne hj) (Fin.castSucc_ne_last j), Fin.snoc_castSucc]

/-- The two completions jointly span all the old columns and the new one. -/
theorem span_completion_sup_replacement (K : Type*) [Semiring K] [Module K V]
    (w : Fin s → V) (i : Fin s) (x : V) :
    span K (range w) ⊔ span K (range (Function.update w i x)) = span K (range (Fin.snoc w x)) := by
  rw [← span_union, Fin.range_snoc]
  congr 1
  ext y
  constructor
  · rintro (hy | ⟨j, rfl⟩)
    · exact Or.inr hy
    · by_cases hj : j = i
      · subst j
        exact Or.inl (Function.update_self ..)
      · exact Or.inr ⟨j, (Function.update_of_ne hj ..).symm⟩
  · rintro (rfl | hy)
    · exact Or.inr ⟨i, Function.update_self ..⟩
    · exact Or.inl hy

end Grassmann

end VPVNP
end Computability
end OAI
