import OAI.Computability.BorderVNP.PackedCells
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# Counting private factors without evaluating boundary parameters

The cell macro rejects a failed Boolean check. A passing assignment records
an exponent for each parameter and a multiplicity for each gadget position.
A zero-valued gadget position is still recorded. Its value is used only
when the aggregate residue matrix entry is read.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing MvPolynomial
open scoped BigOperators Classical

/-- A rejected local assignment or two additive counter vectors. Multiplication
combines independently computed records and propagates failure. -/
abbrev Entry (Param Gadget : Type*) :=
  WithZero (Multiplicative ((Param →₀ ℕ) × (Gadget →₀ ℕ)))

variable {Param Gadget E : Type*} [CommSemiring E]

/-- Encode one passing local tally. -/
def passed (μ : Param →₀ ℕ) (δ : Gadget →₀ ℕ) : Entry Param Gadget :=
  (Multiplicative.ofAdd (μ, δ) : Multiplicative ((Param →₀ ℕ) × (Gadget →₀ ℕ)))

/-- Each used gadget position contributes one to its own counter, even if
the entry at that position is zero in the chosen field. -/
noncomputable def gadget (g : Gadget) : Entry Param Gadget := passed 0 (Finsupp.single g 1)

/-- Entry of the unary polynomial table on its supplied input bit. -/
noncomputable def unary (p : Param) (j : ℕ) (b : Bool) : Entry Param Gadget :=
  if b then passed (Finsupp.single p (2 ^ j)) 0 else 1

/-- Multiply entries after reconstructing the gadget coefficient. No
parameter need have a value in the field at the boundary. -/
noncomputable def interpret (value : Gadget → E) : Entry Param Gadget →*₀ MvPolynomial Param E :=
  WithZero.lift' {
    toFun := fun z => monomial z.toAdd.1 (z.toAdd.2.prod (fun g n => value g ^ n))
    map_one' := by change monomial 0 _ = _; simp
    map_mul' := by
      intro a b
      change monomial (a.toAdd.1 + b.toAdd.1)
        ((a.toAdd.2 + b.toAdd.2).prod (fun g n => value g ^ n)) = _
      rw [monomial_mul_monomial, Finsupp.prod_add_index' (fun _ => pow_zero _)
        (fun _ _ _ => pow_add ..)] }

/-- Reading a passing tag recovers exactly the reconstructed formal monomial. -/
theorem interpret_passed (value : Gadget → E) (μ : Param →₀ ℕ) (δ : Gadget →₀ ℕ) :
    interpret value (passed μ δ) = monomial μ (δ.prod fun g n => value g ^ n) := rfl

/-- The tagged version of an original gadget table position. -/
theorem interpret_gadget (value : Gadget → E) (g : Gadget) :
    interpret (Param := Param) value (gadget g) = C (value g) := by
  rw [gadget, interpret_passed]
  simp

/-- The tagged version of an original polynomial unary table. -/
theorem interpret_unary (value : Gadget → E) (p : Param) (j : ℕ) (b : Bool) :
    interpret value (unary p j b) = if b then X p ^ (2 ^ j) else 1 := by
  cases b <;> simp [unary, interpret_passed, X_pow_eq_monomial]

variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)

/-- Read and multiply all local tagged factors at their actual incidences. -/
noncomputable def assignmentEntry (tags : N.Tables (Entry Param Gadget))
    (inside : N.Assignment) (outside : Ports bits) : Entry Param Gadget :=
  ∏ v, N.read tags inside outside v

/-- The ordinary parameter-ring contraction is the sum of the interpreted
counter records of its complete bit assignments. -/
theorem value_eq_tag_sum (tags : N.Tables (Entry Param Gadget))
    (value : Gadget → E) (outside : Ports bits) :
    N.value (fun v a x => interpret value (tags v a x)) outside =
      ∑ z, interpret value (assignmentEntry N tags z outside) := by
  simp [Network.value, assignmentEntry, Network.read]

/-- Select the passing assignments by their Boolean tests. Rejected
assignments contribute zero, while a recorded scalar that evaluates to
zero still has a passing assignment with its full multiplicities. -/
theorem value_eq_passing_sum (tags : N.Tables (Entry Param Gadget))
    (value : Gadget → E) (outside : Ports bits) :
    N.value (fun v a x => interpret value (tags v a x)) outside =
      ∑ z ∈ Finset.univ.filter (fun z => assignmentEntry N tags z outside ≠ 0),
        interpret value (assignmentEntry N tags z outside) := by
  rw [value_eq_tag_sum]
  apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro z _ hz
  have hzero : assignmentEntry N tags z outside = 0 := by simpa using hz
  rw [hzero, map_zero]

variable {Cell : Type} [Fintype Cell] [DecidableEq Cell]

/-- The tagged product read by one cell, with local wire variables supplied
once via the split of its private and public edge names. -/
noncomputable def cellEntry (cell : N.Site → Cell) (tags : N.Tables (Entry Param Gadget))
    (exterior : N.CrossingAssignment cell) (interior : ∀ c, N.InsideAssignment cell c)
    (x : Ports bits) (c : Cell) : Entry Param Gadget :=
  ∏ v : {v : N.Site // cell v = c},
    N.read tags ((N.cellAssignmentEquiv cell).symm (exterior, interior)) x v.val

/-- Multiplying the per-cell counter records recovers the complete assignment
record. No bit on an edge internal to one cell is counted in another. -/
theorem prod_cellEntry (cell : N.Site → Cell) (tags : N.Tables (Entry Param Gadget))
    (exterior : N.CrossingAssignment cell) (interior : ∀ c, N.InsideAssignment cell c)
    (x : Ports bits) :
    (∏ c, cellEntry N cell tags exterior interior x c) =
      assignmentEntry N tags ((N.cellAssignmentEquiv cell).symm (exterior, interior)) x := by
  exact Fintype.prod_fiberwise cell _

end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
