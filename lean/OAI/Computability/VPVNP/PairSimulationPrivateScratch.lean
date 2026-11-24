import OAI.Computability.VPVNP.PairSimulationHistogramFrame

/-!
# Private arrays and pointwise dependence on the incoming memory

Writing a finite word array replaces precisely its addressed cells. Incrementing
a list of histogram labels depends at each address only on that address's original
contents. These operations describe the scratch state of a successful map call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.PrivateScratch

open BurstRAM
open scoped Fin.CommRing

/-- Contents of private scratch memory as a word-valued function of a machine-word address. -/
abbrev Memory (w : ℕ) := Word w → Word w

variable {w n t : ℕ}

/-- The result of storing all values in a consecutive private array. -/
noncomputable def write (base : Word w) (value : Fin n → Word w) (mem : Memory w) (a : Word w) :
    Word w := by
  classical
  exact if h : ∃ i : Fin n, base + (i.val : Word w) = a then value h.choose else mem a

theorem eq_write (base : Word w) (value : Fin n → Word w) {old new : Memory w}
    (cells : ∀ i : Fin n, new (base + (i.val : Word w)) = value i)
    (frame : ∀ a : Word w, (∀ i : Fin n, a ≠ base + (i.val : Word w)) → new a = old a) :
    new = write base value old := by
  classical
  funext a
  by_cases h : ∃ i : Fin n, base + (i.val : Word w) = a
  · rw [write, dite_eq_left h, ← cells, h.choose_spec]
  · rw [write, dite_eq_right h]
    exact frame a (fun i hi ↦ h ⟨i, hi.symm⟩)

/-- An address distinct from every word in a natural-addressed array is outside
its natural interval. -/
theorem outside_of_ne (base : ℕ) (a : Word w)
    (h : ∀ i : Fin n, a ≠ (base : Word w) + (i.val : Word w)) :
    a.val < base ∨ base + n ≤ a.val := by
  by_contra! hi
  let i : Fin n := ⟨a.val - base, by omega⟩
  apply h i
  rw [← Nat.cast_add, show base + i.val = a.val by dsimp [i]; omega]
  exact Fin.ext (Nat.mod_eq_of_lt a.isLt).symm

theorem write_congr_at (base : Word w) (value : Fin n → Word w) {old old' : Memory w}
    (a : Word w) (h : old a = old' a) : write base value old a = write base value old' a := by
  simp only [write, h]

theorem accumulate_congr_at (base : ℕ) (names : List (Fin t)) {old old' : Memory w}
    (a : Word w) (h : old a = old' a) :
    PrivateLabels.accumulate base names old a = PrivateLabels.accumulate base names old' a := by
  induction names generalizing old old' with
  | nil => exact h
  | cons l ls ih =>
    apply ih
    by_cases he : a = ((base + l.val : ℕ) : Word w)
    · subst a
      simp only [Function.update_self, h]
    · simp only [Function.update_of_ne he, h]

end PairSimulation.PrivateScratch

end VPVNP
end Computability
end OAI
