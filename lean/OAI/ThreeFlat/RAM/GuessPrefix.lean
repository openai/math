import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace OAI
/-! # Partitioning assignments by the next guessed bit -/

namespace ThreeFlat.RAM.Contraction

variable {n : ℕ}

def extensions (t : ℕ) (bits : Fin n → Bool) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun h => ∀ j : Fin n, j.val < t → h j = bits j

theorem extensions_zero (bits : Fin n → Bool) : extensions 0 bits = Finset.univ := by
  ext h
  simp [extensions]

theorem extensions_all (bits : Fin n → Bool) : extensions n bits = {bits} := by
  ext h
  simp only [extensions, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · exact fun e => funext fun j => e j j.isLt
  · rintro rfl j _
    rfl

theorem mem_extensions_succ {h bits : Fin n → Bool} (i : Fin n) (b : Bool) :
    h ∈ extensions (i.val+1) (Function.update bits i b) ↔
      h ∈ extensions i.val bits ∧ h i = b := by
  simp only [extensions, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro e
    refine ⟨?_, by simpa using e i (by omega)⟩
    intro j hj
    simpa [Function.update_of_ne (show j ≠ i from fun eq => by subst j; omega)]
      using e j (by omega)
  · rintro ⟨e, hi⟩ j hj
    by_cases eq : j = i
    · subst j
      simpa using hi
    · rw [Function.update_of_ne eq]
      exact e j (by have := fun h : j.val = i.val => eq (Fin.ext h); omega)

theorem sum_extensions_split {A : Type*} [AddCommMonoid A] (f : (Fin n → Bool) → A)
    (bits : Fin n → Bool) (i : Fin n) :
    (∑ h ∈ extensions i.val bits, f h) =
      (∑ h ∈ extensions (i.val+1) (Function.update bits i false), f h) +
      ∑ h ∈ extensions (i.val+1) (Function.update bits i true), f h := by
  let left := extensions (i.val+1) (Function.update bits i false)
  let right := extensions (i.val+1) (Function.update bits i true)
  have decomp : extensions i.val bits = left ∪ right := by
    ext h
    simp only [left, right, Finset.mem_union, mem_extensions_succ]
    cases h i <;> simp
  have dis : Disjoint left right := by
    apply Finset.disjoint_left.mpr
    intro h hL hR
    have eL := ((mem_extensions_succ i false).mp hL).2
    have eR := ((mem_extensions_succ i true).mp hR).2
    simp [eL] at eR
  rw [decomp, Finset.sum_union dis]

end ThreeFlat.RAM.Contraction

end OAI
