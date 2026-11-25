import OAI.Hierarchy.GridLensSites
import Mathlib.Data.Finset.Sort

namespace OAI
/-! # The first untouched catalyst passages in label order -/

namespace Hierarchy.GridLens

variable {E : Type*} [Fintype E] [LinearOrder E] {k n : ℕ}
variable (direction : E → Fin k) (row : E → Fin k → Fin (n+1)) (touch : E → Option (Fin (n+1)))

/-- The rails in direction `j` passing through `x` whose bits are untouched there. -/
def untouchedRails (x : Fin k → Fin (n+1)) (j : Fin k) : Finset E :=
  Finset.univ.filter fun e => direction e = j ∧ cellOnRail j (row e) (x j) = x ∧ touch e ≠ some (x j)

variable (width : Fin k → ℕ)
variable (capacity : ∀ x j, width j ≤ (untouchedRails direction row touch x j).card)

/-- The `i`th catalyst wire in direction `j` uses the `i`th untouched external label. -/
def firstPassage (x : Fin k → Fin (n+1)) (w : Σ j, Fin (width j)) : E :=
  (untouchedRails direction row touch x w.1).orderEmbOfCardLe (capacity x w.1) w.2

theorem firstPassage_spec (x : Fin k → Fin (n+1)) (w : Σ j, Fin (width j)) :
    let e := firstPassage direction row touch width capacity x w
    direction e = w.1 ∧ cellOnRail w.1 (row e) (x w.1) = x ∧ touch e ≠ some (x w.1) := by
  apply (Finset.mem_filter.mp ((untouchedRails direction row touch x w.1).orderEmbOfCardLe_mem (capacity x w.1) w.2)).2

theorem firstPassage_injective (x : Fin k → Fin (n+1)) :
    Function.Injective (firstPassage direction row touch width capacity x) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have hi := (firstPassage_spec direction row touch width capacity x ⟨i,a⟩).1
  have hj := (firstPassage_spec direction row touch width capacity x ⟨j,b⟩).1
  have hij := hi.symm.trans ((congrArg direction h).trans hj)
  change i = j at hij
  subst j
  exact congrArg (Sigma.mk i) (((untouchedRails direction row touch x i).orderEmbOfCardLe (capacity x i)).injective h)

end Hierarchy.GridLens

end OAI
