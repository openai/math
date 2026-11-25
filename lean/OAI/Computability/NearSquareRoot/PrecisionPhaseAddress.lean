import OAI.Computability.NearSquareRoot.PrecisionPhaseStream
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic

/-! # Addressing the coefficient records of a tensor phase
The list traversed by the physical prefix generator is put in the same
finite-index order used by the Euclidean-space diagonal action. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseStream

/-- Read the array stored in a lexicographic list, with its proved length. -/
def indexed {α : Type*} {n : ℕ} (xs : List α) (h : xs.length = n) (j : Fin n) : α :=
  xs[j.val]'(h ▸ j.isLt)

@[simp] theorem ofFn_indexed {α : Type*} {n : ℕ} (xs : List α) (h : xs.length = n) :
    List.ofFn (indexed xs h) = xs := by
  apply List.ext_getElem
  · simpa using h.symm
  · simp [indexed]

theorem indexed_map {α β : Type*} {n : ℕ} (xs : List α) (h : xs.length = n)
    (f : α → β) (i : Fin n) :
    indexed (xs.map f) (by simpa using h) i = f (indexed xs h i) := by
  simp [indexed]

/-- A pointwise list invariant supplied by a tape-producing pass remains
valid when the same bytes are read as a fixed-width array. -/
theorem indexed_rel {α β : Type*} {n : ℕ} {xs : List α} {ys : List β}
    {R : α → β → Prop} (h : List.Forall₂ R xs ys) (hx : xs.length = n)
    (i : Fin n) : R (indexed xs hx i) (indexed ys (h.length_eq.symm.trans hx) i) :=
  h.get _ _

theorem norm_tensor_entry {α : Type*} (tables : List (List α)) (ideal : α → ℂ)
    (hunit : ∀ t ∈ tables, ∀ a ∈ t, ‖ideal a‖ = 1) {digits : List α}
    (h : digits ∈ addresses tables) : ‖(digits.map ideal).prod‖ = 1 := by
  rw [List.norm_prod, List.map_map]
  have hmap : digits.map ((fun z : ℂ => ‖z‖) ∘ ideal) = digits.map (fun _ => (1 : ℝ)) := by
    apply List.map_congr_left
    exact forall_of_mem_addresses h hunit
  rw [hmap]
  simp

end PhaseStream

end NearSquareRoot
end Computability
end OAI
