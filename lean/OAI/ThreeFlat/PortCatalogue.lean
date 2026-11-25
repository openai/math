import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Lattice.Fold

namespace OAI
/-! # A uniform finite catalogue of port demands

The catalogue depends only on the number of slots. Each entry records the
number of unit wires allocated to an ordered pair of slots.
-/

namespace ThreeFlat

open scoped BigOperators

/-- A code for a square table with entries between zero and `3 * m` inclusive. -/
abbrev PortDemandCode (m : ℕ) := Fin m → Fin m → Fin (3 * m + 1)

namespace PortDemandCode

variable {m : ℕ}

/-- Store a pointwise bounded natural-number table without changing its entries. -/
def encode (r : Fin m → Fin m → ℕ) (bound : ∀ i j, r i j ≤ 3 * m) : PortDemandCode m :=
  fun i j => ⟨r i j, Nat.lt_succ_of_le (bound i j)⟩

@[simp] theorem encode_val (r : Fin m → Fin m → ℕ) (bound : ∀ i j, r i j ≤ 3 * m)
    (i j : Fin m) : ((encode r bound i j : Fin (3 * m + 1)) : ℕ) = r i j := rfl

/-- Each of the `m * m` entries has `3 * m + 1` choices. -/
theorem card (m : ℕ) : Fintype.card (PortDemandCode m) = (3 * m + 1) ^ (m * m) := by
  simp only [PortDemandCode, Fintype.card_fun, Fintype.card_fin, pow_mul]

/-- The total demand leaving or entering any one slot is at most `4 * m`. -/
abbrev Admissible (c : PortDemandCode m) : Prop :=
  (∀ i, (∑ j, (c i j : ℕ)) ≤ 4 * m) ∧ (∀ j, (∑ i, (c i j : ℕ)) ≤ 4 * m)

end PortDemandCode

/-- The finite catalogue of codes obeying the rounded port budget. -/
abbrev BoundedPortDemand (m : ℕ) := {c : PortDemandCode m // c.Admissible}

namespace BoundedPortDemand

variable {m : ℕ}

/-- Place a bounded table with the required row and column capacities in the catalogue. -/
def encode (r : Fin m → Fin m → ℕ) (bound : ∀ i j, r i j ≤ 3 * m)
    (rows : ∀ i, (∑ j, r i j) ≤ 4 * m) (cols : ∀ j, (∑ i, r i j) ≤ 4 * m) :
    BoundedPortDemand m :=
  ⟨PortDemandCode.encode r bound, rows, cols⟩

@[simp] theorem encode_val (r : Fin m → Fin m → ℕ) (bound : ∀ i j, r i j ≤ 3 * m)
    (rows : ∀ i, (∑ j, r i j) ≤ 4 * m) (cols : ∀ j, (∑ i, r i j) ≤ 4 * m)
    (i j : Fin m) : ((encode r bound rows cols).val i j : ℕ) = r i j := rfl

/-- Every catalogue entry has at most `8 * m` incoming and outgoing unit port
ends combined at a given position. A diagonal entry contributes to both sums. -/
theorem incident_le (c : BoundedPortDemand m) (i : Fin m) :
    (∑ j, (c.val i j : ℕ)) + (∑ j, (c.val j i : ℕ)) ≤ 8 * m := by
  simpa only [← Nat.add_mul] using Nat.add_le_add (c.property.1 i) (c.property.2 i)

/-- The number of admissible codes is bounded independently of the demand widths. -/
theorem card_le (m : ℕ) : Fintype.card (BoundedPortDemand m) ≤ (3 * m + 1) ^ (m * m) :=
  (Fintype.card_subtype_le (PortDemandCode.Admissible (m := m))).trans_eq (PortDemandCode.card m)

/-- A per-code threshold for repeating and padding tiles gives a single
threshold for the entire graph. -/
theorem exists_uniform_threshold (p : BoundedPortDemand m → ℕ → Prop)
    (eventually : ∀ c, ∃ t, ∀ v ≥ t, p c v) : ∃ t, ∀ c, ∀ v ≥ t, p c v := by
  classical
  let t := fun c => Classical.choose (eventually c)
  refine ⟨Finset.univ.sup t, fun c v hv => Classical.choose_spec (eventually c) v ?_⟩
  exact (Finset.le_sup (f := t) (Finset.mem_univ c)).trans hv

end BoundedPortDemand

end ThreeFlat

end OAI
