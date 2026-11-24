import OAI.Computability.VPVNP.PairSimulationPrivateLabels

/-!
# Private memory outside the histogram

The label loop changes one word per emitted name. The remaining addresses
retain their exact initial contents on the same path.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.PrivateLabels

open BurstRAM
open scoped Fin.CommRing

variable {w t : ℕ}

theorem accumulate_outside (base : ℕ) (names : List (Fin t)) (mem : Word w → Word w)
    (addr : Word w) (apart : ∀ i : Fin t, addr ≠ ((base + i.val : ℕ) : Word w)) :
    accumulate base names mem addr = mem addr := by
  induction names generalizing mem with
  | nil => rfl
  | cons i names ih =>
    rw [accumulate, ih]
    exact Function.update_of_ne (apart i) ..

end PairSimulation.PrivateLabels

end VPVNP
end Computability
end OAI
