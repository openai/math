import OAI.Hierarchy.GridThrough
import OAI.Hierarchy.GridPassageSelection

namespace OAI
/-! # Reserving catalyst passages in a legal programmed setting -/

namespace Hierarchy.GridThrough.Program
open GridLens

variable {E : Type} [Fintype E] [LinearOrder E] {k n p : ℕ}

/-- The first untouched rails in label order produce the actual program's catalyst field.
The touch map and data-pin assignments come from the selected controller setting. -/
def ofUntouched (direction : E → Fin k) (row : E → Cell k n) (touch : E → Option (Fin (n+1)))
    (width : Fin k → ℕ) (capacity : ∀ x j, width j ≤ (untouchedRails direction row touch x j).card)
    (data : Cell k n → Fin p → (Touch touch × Bool) ⊕ Bool)
    (data_cell : ∀ c i u, data c i = .inl u → cellOnRail (direction u.1.val.1) (row u.1.val.1) u.1.val.2 = c)
    (data_once : ∀ u, ∃! ci : Cell k n × Fin p, data ci.1 ci.2 = .inl u) :
    GridThrough.Program E n p width where
  direction := direction
  row := row
  touch := touch
  data := data
  data_cell := data_cell
  data_once := data_once
  pass := firstPassage direction row touch width capacity
  pass_injective := firstPassage_injective direction row touch width capacity
  pass_dir c w := (firstPassage_spec direction row touch width capacity c w).1
  pass_line c w := by
    have h := firstPassage_spec direction row touch width capacity c w
    change cellOnRail (direction (firstPassage direction row touch width capacity c w)) _
      (c (direction (firstPassage direction row touch width capacity c w))) = c
    rw [h.1]
    exact h.2.1
  pass_untouched c w := by
    have h := firstPassage_spec direction row touch width capacity c w
    change touch _ ≠ some (c (direction (firstPassage direction row touch width capacity c w)))
    rw [h.1]
    exact h.2.2

end Hierarchy.GridThrough.Program

end OAI
