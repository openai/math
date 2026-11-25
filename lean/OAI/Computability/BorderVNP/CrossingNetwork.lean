import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Placed bit-cable networks with external ports

Each cable carries a word of a fixed integral width. Both endpoint tables
read the same word, and the contraction sums once over all cable words.
A vertex table can read only its incident cables and its own external ports.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open scoped BigOperators

/-- A finite network layout in a Euclidean unit ball. Each external port is a bit bundle. -/
structure Network (D : ℕ) (P : Type*) (bits : P → ℕ) where
  /-- Local tensor sites. -/
  Site : Type
  /-- Internal cables. -/
  Edge : Type
  finiteSite : Fintype Site
  finiteEdge : Fintype Edge
  /-- Initial endpoint of an internal cable. -/
  src : Edge → Site
  /-- Final endpoint of an internal cable. -/
  dst : Edge → Site
  /-- Integral width of each internal cable. -/
  width : Edge → ℕ
  /-- Site at which an external port is attached. -/
  attach : P → Site
  /-- Euclidean position of each site. -/
  position : Site → EuclideanSpace ℝ (Fin D)
  in_ball : ∀ v, ‖position v‖ ≤ 1

attribute [instance] Network.finiteSite Network.finiteEdge

variable {D : ℕ} {P : Type*} {bits : P → ℕ}

/-- The bit strings on all external ports. -/
abbrev Ports (bits : P → ℕ) := ∀ p, Fin (bits p) → Bool

/-- The internal indices of a contraction, shared by the two endpoints. -/
abbrev Network.Assignment (N : Network D P bits) := ∀ e : N.Edge, Fin (N.width e) → Bool

/-- Exactly the internal and external indices visible to each local tensor. -/
abbrev Network.Tables (N : Network D P bits) (K : Type*) :=
  ∀ v : N.Site,
    (∀ e : {e : N.Edge // N.src e = v ∨ N.dst e = v}, Fin (N.width e.val) → Bool) →
    (∀ p : {p : P // N.attach p = v}, Fin (bits p.val) → Bool) → K

/-- Restrict a whole assignment to the local table at a site. -/
def Network.read {K : Type*} (N : Network D P bits) (table : N.Tables K)
    (a : N.Assignment) (x : Ports bits) (v : N.Site) : K :=
  table v (fun e => a e.val) (fun p => x p.val)

/-- The tensor computed on the external ports by summing all internal words. -/
noncomputable def Network.value {K : Type*} [CommSemiring K] (N : Network D P bits)
    (table : N.Tables K) (x : Ports bits) : K := by
  classical
  exact ∑ a : N.Assignment, ∏ v : N.Site, N.read table a x v

/-- Total width-weighted Euclidean length of the internal cables. -/
noncomputable def Network.cost (N : Network D P bits) : ℝ :=
  ∑ e : N.Edge, (N.width e : ℝ) * dist (N.position (N.src e)) (N.position (N.dst e))

/-- Fixed placements of the external ports may coincide. -/
def Network.PlacedAt (N : Network D P bits) (place : P → EuclideanSpace ℝ (Fin D)) : Prop :=
  ∀ p, N.position (N.attach p) = place p

end Crossing

end BorderVNP
end Computability
end OAI
