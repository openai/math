import Mathlib.Data.Finset.Basic

/-! # Local incidence conditions for ordered grammar parses

An event names a half-open interval of leaves by its starting offset and its length
minus one. A binary event requests precisely its two ordered child intervals.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar

/-- A candidate production occurrence in an ordered parse, recording a leaf interval, the state
at its root and the production used there. -/
structure ParseEvent (V H : Type*) where
  /-- The zero-based offset of the first leaf in the occurrence. -/
  start : ℕ
  /-- The length of the occurrence's leaf interval minus one. -/
  layer : ℕ
  /-- The grammar state at the root of the occurrence. -/
  state : H
  /-- The terminal variable emitted by a leaf, or the left child's layer and the ordered pair
  of child states at a binary node. -/
  production : V ⊕ (ℕ × H × H)
  deriving DecidableEq

variable {V H : Type*}

/-- A terminal has one leaf. A binary split has two positive child lengths. -/
def ParseEvent.WellFormed (e : ParseEvent V H) : Prop :=
  match e.production with
  | .inl _ => e.layer = 0
  | .inr (b, _, _) => b < e.layer

/-- An occurrence matches a requested interval and state when its start, layer and root state
agree with all three arguments. -/
def ParseEvent.Matches (e : ParseEvent V H) (l d : ℕ) (h : H) : Prop :=
  e.start = l ∧ e.layer = d ∧ e.state = h

/-- A binary occurrence requests its two ordered child intervals and their states. A terminal
occurrence has no child requests. -/
def ParseEvent.Requests (e : ParseEvent V H) (l d : ℕ) (h : H) : Prop :=
  match e.production with
  | .inl _ => False
  | .inr (b, i, j) => (l = e.start ∧ d = b ∧ h = i) ∨
      (l = e.start + b + 1 ∧ d = e.layer - b - 1 ∧ h = j)

/-- Exactly one production at every occupied interval, with the designated root and
both children of each binary production. Every other event has an incoming request. -/
structure IsParseTable (T : Finset (ParseEvent V H)) (l d : ℕ) (h : H) : Prop where
  root : ∃ e ∈ T, e.Matches l d h
  typed : ∀ e ∈ T, e.WellFormed
  unique : ∀ e ∈ T, ∀ f ∈ T, e.start = f.start → e.layer = f.layer → e = f
  children : ∀ e ∈ T, ∀ l d h, e.Requests l d h → ∃ f ∈ T, f.Matches l d h
  parent : ∀ e ∈ T, e.Matches l d h ∨ ∃ f ∈ T, f.Requests e.start e.layer e.state

end ParseGrammar

end VPVNP
end Computability
end OAI
