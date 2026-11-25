import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Finset.Card

/-! The single-coordinate oracle of Theorem 1.3. A branch may depend on the entire transcript. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame

/-- One rational price vector and the coordinate whose label is requested. -/
structure Query (N : ℕ) where
  prices : Fin N → ℚ
  index : Fin N

/-- Hidden costs outside the active set are immaterial. -/
structure Hidden (N R : ℕ) (anchor : Fin N) where
  positive : Bool
  active : Finset (Fin N)
  anchor_mem : anchor ∈ active
  cost : Fin N → Fin (R + 1)

namespace Hidden

variable {N R : ℕ} {anchor : Fin N}

def signedPrice (h : Hidden N R anchor) (t : ℚ) : ℚ := if h.positive then t else -t

/-- Exactly the designated active minimizers must reveal the sign, including ties. -/
def Forced (h : Hidden N R anchor) (q : Query N) : Prop :=
  q.index ∈ h.active ∧ ∀ j ∈ h.active,
    (h.cost q.index : ℕ) + h.signedPrice (q.prices q.index) ≤
      (h.cost j : ℕ) + h.signedPrice (q.prices j)

end Hidden

/-- A finite adaptive strategy. Its height charges queries even for inconsistent replies. -/
inductive Tree (N : ℕ) where
  | result (answer : Bool)
  | ask (query : Query N) (next : Bool → Tree N)

namespace Tree

variable {N R : ℕ} {anchor : Fin N}

/-- Different occurrences of an unforced query may receive different labels. -/
inductive Reaches (h : Hidden N R anchor) : Tree N → Bool → Prop where
  | result (answer : Bool) : Reaches h (.result answer) answer
  | ask {q : Query N} {next : Bool → Tree N} {reply answer : Bool}
      (allowed : h.Forced q → reply = h.positive) (rest : Reaches h (next reply) answer) :
      Reaches h (.ask q next) answer

def Correct (h : Hidden N R anchor) (t : Tree N) : Prop :=
  ∀ answer, Reaches h t answer → answer = h.positive

/-- Worst-case oracle query count. -/
def height : Tree N → ℕ
  | .result _ => 0
  | .ask _ next => max (height (next false)) (height (next true)) + 1

/-- The reply may depend on the entire reverse-chronological transcript. -/
def run (reply : List (Query N × Bool) → Query N → Bool) (t : Tree N)
    (history : List (Query N × Bool) := []) : Bool :=
  match t with
  | .result answer => answer
  | .ask q next =>
    let b := reply history q
    run reply (next b) ((q, b) :: history)

theorem reaches_run (h : Hidden N R anchor)
    (reply : List (Query N × Bool) → Query N → Bool)
    (valid : ∀ history q, h.Forced q → reply history q = h.positive)
    (t : Tree N) (history : List (Query N × Bool)) :
    Reaches h t (run reply t history) := by
  induction t generalizing history with
  | result answer => exact .result answer
  | ask q next ih => exact .ask (valid history q) (ih (reply history q) _)

theorem run_eq_of_correct (h : Hidden N R anchor) (t : Tree N) (correct : Correct h t)
    (reply : List (Query N × Bool) → Query N → Bool)
    (valid : ∀ history q, h.Forced q → reply history q = h.positive) :
    run reply t [] = h.positive :=
  correct _ (reaches_run h reply valid t [])

end Tree
end PriceGame
end LinearProgramming
end Optimization
end OAI
