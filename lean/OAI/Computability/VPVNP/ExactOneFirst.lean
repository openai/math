import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.FinRange

/-!
# Selecting the first satisfied literal

Each literal occurrence is indexed by its position. In a satisfied clause, the
first match is unique even when the same literal occurs at several positions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ExactOne

variable {m : ℕ}

/-- A true bit with no earlier true bit. -/
def firstMatch (f : Fin m → Bool) (i : Fin m) : Bool :=
  decide (f i = true ∧ ∀ j < i, f j = false)

theorem firstMatch_iff (f : Fin m → Bool) (i : Fin m) :
    firstMatch f i = true ↔ f i = true ∧ ∀ j < i, f j = false := by
  simp [firstMatch]

theorem firstMatch_unique (f : Fin m → Bool) {i j : Fin m}
    (hi : firstMatch f i = true) (hj : firstMatch f j = true) : i = j := by
  rw [firstMatch_iff] at hi hj
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (by simpa [hi.1] using hj.2 i h)
  · exact h
  · exact False.elim (by simpa [hj.1] using hi.2 j h)

theorem existsUnique_firstMatch (f : Fin m → Bool) (hf : ∃ i, f i = true) :
    ∃! i, firstMatch f i = true := by
  let s := Finset.univ.filter (fun i => f i = true)
  have hs : s.Nonempty := by simpa [s, Finset.Nonempty] using hf
  let i := s.min' hs
  have hi : firstMatch f i = true := by
    rw [firstMatch_iff]
    refine ⟨by simpa [s] using s.min'_mem hs, fun j hj => ?_⟩
    cases h : f j with
    | false => rfl
    | true => exact (not_le_of_gt hj (s.min'_le j (by simp [s, h]))).elim
  exact ⟨i, hi, fun j hj => firstMatch_unique f hj hi⟩

theorem countP_finRange_eq_one (f : Fin m → Bool) :
    (List.finRange m).countP f = 1 ↔ ∃! i, f i = true := by
  have h := (List.nodup_finRange m).card_eq_countP (P := fun i => f i = true)
  simp only [Bool.decide_eq_true] at h
  rw [← h, Finset.card_eq_one_iff_existsUnique]
  simp

end ExactOne

end VPVNP
end Computability
end OAI
