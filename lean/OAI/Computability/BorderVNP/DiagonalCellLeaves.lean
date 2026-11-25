import OAI.Computability.BorderVNP.DiagonalCellEntries
import OAI.Computability.BorderVNP.CrossingProfileValue
import OAI.Computability.BorderVNP.CrossingProfileScan

/-! # Reading the expanded factors in one private cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing

/-- The three events recorded by the bit checker after it reads the private
assignment and routes any selector subsequence. -/
inductive Leaf (Param Gadget : Type*)
  | check (accepted : Bool)
  | scalar (position : Gadget)
  | power (parameter : Param) (place : ℕ) (selected : Bool)
  deriving DecidableEq

variable {Param Gadget E : Type*}

/-- A scalar entry is counted independently of its value. Only a failed
Boolean gate, equality, histogram or pin test rejects the assignment. -/
def Leaf.accepted : Leaf Param Gadget → Bool
  | .check ok => ok
  | .scalar .. | .power .. => true

/-- A surviving unary factor supplies its parameter and the binary power
that it contributed. -/
def Leaf.powerEvent : Leaf Param Gadget → Option (Param × ℕ)
  | .power p j true => some (p, 2 ^ j)
  | _ => none

/-- A lookup of a fixed table records its exact position. -/
def Leaf.scalarEvent : Leaf Param Gadget → Option Gadget
  | .scalar g => some g
  | _ => none

/-- Mathematical tagged value of one expanded local observation. -/
noncomputable def Leaf.entry : Leaf Param Gadget → Entry Param Gadget
  | .check b => if b then 1 else 0
  | .scalar g => gadget g
  | .power p j b => unary p j b

/-- Accumulate the actual selected powers in a polynomial exponent. -/
noncomputable def powerCounts (ls : List (Leaf Param Gadget)) : Param →₀ ℕ :=
  ((ls.filterMap Leaf.powerEvent).map (fun z => Finsupp.single z.1 z.2)).sum

/-- Accumulate each occurrence of a gadget position, including repetitions. -/
noncomputable def scalarCounts (ls : List (Leaf Param Gadget)) : Gadget →₀ ℕ :=
  ((ls.filterMap Leaf.scalarEvent).map (fun g => Finsupp.single g 1)).sum

private theorem passed_mul (x y : Param →₀ ℕ) (a b : Gadget →₀ ℕ) :
    passed x a * passed y b = passed (x+y) (a+b) := rfl

/-- A private scan's Boolean flag and counter arrays recover the same
tagged product as multiplying every expanded local factor separately. -/
theorem list_entries (ls : List (Leaf Param Gadget)) :
    (ls.map Leaf.entry).prod =
      if ls.all Leaf.accepted then passed (powerCounts ls) (scalarCounts ls) else 0 := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    cases h : ls.all Leaf.accepted <;> cases l with
    | check b =>
      cases b <;> simp [ih, h, Leaf.entry, Leaf.accepted, powerCounts, scalarCounts,
        List.filterMap_cons, Leaf.powerEvent, Leaf.scalarEvent]
    | scalar g =>
      simp [ih, h, Leaf.entry, Leaf.accepted, gadget, passed_mul, powerCounts, scalarCounts,
        List.filterMap_cons, Leaf.powerEvent, Leaf.scalarEvent]
    | power p j b =>
      cases b <;> simp [ih, h, Leaf.entry, Leaf.accepted, unary, passed_mul, powerCounts,
        scalarCounts, List.filterMap_cons, Leaf.powerEvent, Leaf.scalarEvent]

/-- The local check on a passing assignment forces *both* tallies to their
unique values. Passing a zero gadget scalar cannot change these tallies. -/
theorem claimed_iff (ls : List (Leaf Param Gadget)) (μ : Param →₀ ℕ) (δ : Gadget →₀ ℕ) :
    (ls.map Leaf.entry).prod = passed μ δ ↔
      ls.all Leaf.accepted = true ∧ powerCounts ls = μ ∧ scalarCounts ls = δ := by
  rw [list_entries]
  cases h : ls.all Leaf.accepted <;> simp [passed]

variable {A D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} [CommSemiring E]

/-- The existing physical profile tables can be run directly on counter
records. At their origin and terminals the tests are Boolean, and inside
the term bank they multiply the records of the chosen one-copy table. -/
theorem interpret_profile (N : Fin A → Network D P bits)
    (place : P → EuclideanSpace ℝ (Fin D)) (hball : ∀ u, ‖place u‖ ≤ 1)
    (j : ℕ) (p : Fin A → ℕ) (first : P) (tags : ∀ a, (N a).Tables (Entry Param Gadget))
    (values : Gadget → E) (site : (Profile.network N place hball j p).Site) (y x) :
    interpret values (Profile.tables N place hball j p first tags site y x) =
      Profile.tables N place hball j p first (fun a v z e => interpret values (tags a v z e))
        site y x :=
  Profile.map_tables N place hball j p first tags (interpret values) site y x

end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
