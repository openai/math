import OAI.Computability.BorderVNP.CubePhysicalContraction
import OAI.Computability.BorderVNP.CubePhysicalDeclarationWords
import OAI.Computability.BorderVNP.CubePhysicalScheduleBudget

/-! # Broadcast length declarations on the actual cube contraction paths

The public declaration is guessed before the team-private choices. A passing
guess is forced by the path's own packet selectors. Interchanging the finite
sums therefore preserves the contraction and each individual formal coefficient.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open Crossing Diagonal.CellEntries MvPolynomial
open scoped Classical

set_option synthInstance.maxSize 768

variable {n d blocks b h K s D : ℕ} {P : Type*} {bits : P → ℕ}
variable {Cell : Type} [Fintype Cell] [DecidableEq Cell]
variable (N : Network D P bits) (cell : N.Site → Cell)

/-- Read the tuple of selected ordinary cube summands from a physical path. -/
abbrev pathSelectors (a : Path N cell n d blocks b h K s) : Packet n d blocks → Selector n K h :=
  a.2.2.2.1

omit [Fintype Cell] [DecidableEq Cell] in
/-- Exactly one raw length broadcast passes for this physical path, even if
other paths carry the same tuple of selectors. -/
theorem unique_path_broadcast (a : Path N cell n d blocks b h K s) :
    ∃! raw : Broadcast n d (declarationCap n d blocks b h s),
      passesBroadcast b s (pathSelectors N cell a) raw :=
  unique_passing_broadcast ..

variable {Param Gadget E : Type*} [CommRing E]

/-- The actual network value equals the sum with the public binary broadcast
guessed first, followed by the team-private path choices and their checks. -/
theorem value_eq_declared_paths (slot : LiveBit N cell ↪ Slot n d blocks (h*b))
    (tags : N.Tables (Entry Param Gadget)) (x : Ports bits)
    (pos : Packet n d blocks → TableEntry n b h K s → Gadget)
    (values : Gadget → E) (ht : ∀ i, ValidTables (values ∘ pos i)) :
    N.value (fun v r p => interpret values (tags v r p)) x =
      ∑ raw : Broadcast n d (declarationCap n d blocks b h s),
        ∑ a : Path N cell n d blocks b h K s,
          if passesBroadcast b s (pathSelectors N cell a) raw then
            interpret values (pathTag N cell slot tags x pos a) else 0 := by
  rw [value_eq_physical_paths N cell slot tags x pos values ht, Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => (sum_passing_broadcast b s (pathSelectors N cell a) _).symm

/-- Equation (11.2) retains its passing-tag, exponent and gadget counts after
the guessed broadcast is included in the path enumeration. -/
theorem coefficient_eq_declared_paths (slot : LiveBit N cell ↪ Slot n d blocks (h*b))
    (tags : N.Tables (Entry Param Gadget)) (x : Ports bits)
    (pos : Packet n d blocks → TableEntry n b h K s → Gadget)
    (values : Gadget → E) (ht : ∀ i, ValidTables (values ∘ pos i)) (μ : Param →₀ ℕ) :
    let record := pathTag N cell slot tags x pos
    (N.value (fun v r p => interpret values (tags v r p)) x).coeff μ =
      ∑ raw : Broadcast n d (declarationCap n d blocks b h s),
        ∑ a ∈ Finset.univ.filter (fun a : Path N cell n d blocks b h K s =>
          record a ≠ 0 ∧ (counters (record a)).1 = μ),
          if passesBroadcast b s (pathSelectors N cell a) raw then
            (counters (record a)).2.prod fun g k => values g ^ k else 0 := by
  dsimp only
  rw [coefficient_eq_passing_paths N cell slot tags x pos values ht, Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => (sum_passing_broadcast b s (pathSelectors N cell a) _).symm

end Cube.Physical

end BorderVNP
end Computability
end OAI
