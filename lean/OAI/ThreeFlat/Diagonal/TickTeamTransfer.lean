import OAI.ThreeFlat.Diagonal.TickPins
import OAI.ThreeFlat.Diagonal.TickAuxProjection
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace OAI
/-! # Multiplying the physical teams at one transition -/

namespace ThreeFlat.Diagonal.TickTeamTransfer

open TickAuxiliary TickChronology
open scoped Classical BigOperators

section
variable {F : Type*} [CommSemiring F] {teams : ℕ}

/-- A common endpoint check contributes a single indicator to the product
of the weighted teams. Positivity is needed precisely for the rejected case. -/
theorem repeated_guard (pos : 0 < teams) (ok : Prop) [Decidable ok] (factor : Fin teams → F) :
    (∏ j, if ok then factor j else 0) = if ok then ∏ j, factor j else 0 := by
  by_cases h : ok
  · simp [h]
  · simp [h, Nat.ne_of_gt pos]

/-- A terminal cell has exactly one processor owner at the selected time. -/
theorem local_product {Cell : Type*} [Fintype Cell] (owner : Cell → Fin teams)
    (cell : Cell → F) (pos : 0<teams) (ok : Prop) [Decidable ok] :
    (∏ j : Fin teams, if ok then ∏ i : {i : Cell // owner i = j}, cell i.val else 0) =
      if ok then ∏ i, cell i else 0 := by
  rw [repeated_guard pos]
  rw [Fintype.prod_fiberwise owner cell]

end

variable {F : Type*} [Field F] {a teams p n : ℕ}

/-- The physical teams all inspect the same branch marker. Their product
keeps one copy of the history guard and all independent local cell factors. -/
theorem team_entry {Cell : Type*} [Fintype Cell] {S : Type*}
    (N : BitNetwork F p)
    (pin : Fin n → Fin teams → S → S → (Fin a → Bool) → (Fin a → Bool) → Fin p → Bool)
    (t : Fin n) (x y : S) (old new : Fin a → Bool) (L : Layout a) (ph : Phase)
    (owner : Cell → Fin teams) (cell : Cell → F) (pos : 0<teams)
    (admitted chunk idChunk : Prop) [Decidable admitted] [Decidable chunk] [Decidable idChunk]
    (h : ∀ (j : Fin teams), N.eval (pin t j x y old new) =
      if branch L ph old new then
        if L.accepts ph true old new ∧ admitted ∧ chunk then
          ∏ i : {i : Cell // owner i = j}, cell i.val else 0
      else if old = (fun _ => false) ∧ new = (fun _ => false) ∧ idChunk then 1 else 0) :
    teamTick N pin t x y old new =
      if branch L ph old new then
        if phaseFields L ph (project L old) (project L new) ∧ admitted ∧ chunk then ∏ i, cell i else 0
      else if old = (fun _ => false) ∧ new = (fun _ => false) ∧ idChunk then 1 else 0 := by
  classical
  unfold teamTick
  simp_rw [h]
  cases hb : branch L ph old new
  · simp only [Bool.false_eq_true,ite_false]
    rw [repeated_guard pos]
    simp
  · simp only [ite_true]
    rw [local_product owner cell pos,accepts_phase]

end ThreeFlat.Diagonal.TickTeamTransfer

end OAI
