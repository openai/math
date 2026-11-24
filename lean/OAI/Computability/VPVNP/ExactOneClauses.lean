import OAI.Computability.VPVNP.HardnessCNF
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-!
# Exact-one clauses for a CNF verifier

Each clause selects one literal occurrence. Its selector requires that occurrence
to be true and all earlier occurrences to be false. Each implication uses one
filler bit in an exact-one triple. Pairs outside the triangular part of the table
receive a singleton constraint fixing their filler to false.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ExactOne

open HardnessCNF
variable {k : ℕ}

/-- An exact-one constraint counts literal occurrences, including repetitions. -/
def Holds (φ : CNF k) (x : Fin k → Bool) : Prop :=
  ∀ c ∈ φ, c.countP (fun l => x l.1 == l.2) = 1

/-- A literal occurrence identified by its clause and its position within that clause. -/
abbrev Occ (φ : CNF k) := Σ c : Fin φ.length, Fin (φ[c].length)

/-- An ordered pair of literal occurrences in the same clause, including pairs with equal
positions. -/
abbrev PairOcc (φ : CNF k) := Σ c : Fin φ.length, Fin (φ[c].length) × Fin (φ[c].length)

/-- Variables of the exact-one encoding, partitioned into original data bits, occurrence
selectors, and pair fillers. -/
abbrev Slot (φ : CNF k) := Fin k ⊕ (Occ φ ⊕ PairOcc φ)

/-- Total number of Boolean variables in the exact-one encoding of the formula. -/
def width (φ : CNF k) := Fintype.card (Slot φ)

/-- Number the three kinds of exact-one variables by finite ordinals. -/
noncomputable def index (φ : CNF k) : Slot φ ≃ Fin (width φ) := Fintype.equivFin _

/-- Variable index in the exact-one encoding that carries the original Boolean variable `v`. -/
noncomputable def data (φ : CNF k) (v : Fin k) : Fin (width φ) := index φ (.inl v)

/-- Variable index marking occurrence `i` as the selected literal in clause `c`. -/
noncomputable def selector (φ : CNF k) (c : Fin φ.length) (i : Fin (φ[c].length)) :
    Fin (width φ) := index φ (.inr (.inl ⟨c,i⟩))

/-- Variable index for the filler attached to ordered positions `i,j` in clause `c`. -/
noncomputable def filler (φ : CNF k) (c : Fin φ.length) (i j : Fin (φ[c].length)) :
    Fin (width φ) := index φ (.inr (.inr ⟨c,i,j⟩))

/-- Recover the original assignment from an assignment to the enlarged exact-one variable set. -/
noncomputable def original (φ : CNF k) (x : Fin (width φ) → Bool) : Fin k → Bool :=
  x ∘ data φ

/-- Bit required by selector `i` when testing occurrence `j ≤ i`. -/
def needed (φ : CNF k) (y : Fin k → Bool) (c : Fin φ.length) (i j : Fin (φ[c].length)) :
    Bool :=
  let l := φ[c][j]
  if j = i then y l.1 == l.2 else !(y l.1 == l.2)

/-- Clause of positive occurrence selectors requiring exactly one selected position in the
original clause. -/
noncomputable def selectorClause (φ : CNF k) (c : Fin φ.length) : List (Literal (width φ)) :=
  (List.finRange (φ[c].length)).map fun i => (selector φ c i, true)

/-- Exact-one constraint comparing a candidate selector at `i` with occurrence `j`, with a
filler bit making the choice canonical. -/
noncomputable def pairClause (φ : CNF k) (c : Fin φ.length) (i j : Fin (φ[c].length)) :
    List (Literal (width φ)) :=
  let l := φ[c][j]
  if j ≤ i then [(selector φ c i, true), (data φ l.1, if j = i then !l.2 else l.2),
    (filler φ c i j, true)]
  else [(filler φ c i j, false)]

/-- The selector clause and all ordered-pair constraints for one clause of the original
formula. -/
noncomputable def rows (φ : CNF k) (c : Fin φ.length) : CNF (width φ) :=
  selectorClause φ c :: (List.finRange (φ[c].length)).flatMap fun i =>
    (List.finRange (φ[c].length)).map (pairClause φ c i)

/-- Polynomial-size exact-one CNF with original, selector and filler variables. -/
noncomputable def augment (φ : CNF k) : CNF (width φ) :=
  (List.finRange φ.length).flatMap (rows φ)

/-- Exactly one occurrence selector in clause `c` is true under assignment `x`. -/
noncomputable def selectedOnce (φ : CNF k) (x : Fin (width φ) → Bool) (c : Fin φ.length) : Prop :=
  (List.finRange (φ[c].length)).countP (fun i => x (selector φ c i)) = 1

private def exactlyOne {n : ℕ} (x : Fin n → Bool) (c : List (Literal n)) : Prop :=
  c.countP (fun l => x l.1 == l.2) = 1

private theorem exactlyOne_selector (φ : CNF k) (x : Fin (width φ) → Bool)
    (c : Fin φ.length) : exactlyOne x (selectorClause φ c) ↔ selectedOnce φ x c := by
  simp [exactlyOne, selectorClause, selectedOnce, List.countP_map, Function.comp_def]

private theorem triple (a b f : Bool) :
    ((if f then 1 else 0) + (if !b then 1 else 0) + (if a then 1 else 0) = 1) ↔
      (a = true → b = true) ∧ f = (b && !a) := by
  cases a <;> cases b <;> cases f <;> decide

private theorem exactlyOne_pair (φ : CNF k) (x : Fin (width φ) → Bool)
    (c : Fin φ.length) (i j : Fin (φ[c].length)) :
    exactlyOne x (pairClause φ c i j) ↔
      if j ≤ i then
        (x (selector φ c i) = true → needed φ (original φ x) c i j = true) ∧
        x (filler φ c i j) = (needed φ (original φ x) c i j && !(x (selector φ c i)))
      else x (filler φ c i j) = false := by
  by_cases hji : j ≤ i
  · have complement :
        (x (data φ (φ[c][j]).1) == (if j = i then !(φ[c][j]).2 else (φ[c][j]).2)) =
          !(needed φ (original φ x) c i j) := by
      unfold needed original
      simp only [Function.comp_apply]
      split <;> cases h : x (data φ (φ[c][j]).1) <;> cases hp : (φ[c][j]).2 <;> rfl
    simp only [exactlyOne, pairClause, ite_eq_left hji, List.countP_cons, List.countP_nil,
      Nat.zero_add, complement, beq_iff_eq]
    exact triple _ _ _
  · cases hx : x (filler φ c i j) <;> simp [exactlyOne, pairClause, hji, hx]

/-- Exact-one satisfaction determines one selector per clause, forces the tested
literal or its negation when that selector is true, and determines every filler bit. -/
theorem holds_augment_iff (φ : CNF k) (x : Fin (width φ) → Bool) :
    Holds (augment φ) x ↔ (∀ c, selectedOnce φ x c) ∧ ∀ c i j,
      if j ≤ i then
        (x (selector φ c i) = true → needed φ (original φ x) c i j = true) ∧
        x (filler φ c i j) = (needed φ (original φ x) c i j && !(x (selector φ c i)))
      else x (filler φ c i j) = false := by
  change (∀ row ∈ augment φ, exactlyOne x row) ↔ _
  have hh : (∀ row ∈ augment φ, exactlyOne x row) ↔
      ∀ c, exactlyOne x (selectorClause φ c) ∧ ∀ i j, exactlyOne x (pairClause φ c i j) := by
    simp only [augment, rows, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
      List.mem_map, forall_exists_index, or_imp, forall_and]
    aesop
  rw [hh]
  simp only [exactlyOne_selector, exactlyOne_pair, forall_and]

end ExactOne

end VPVNP
end Computability
end OAI
