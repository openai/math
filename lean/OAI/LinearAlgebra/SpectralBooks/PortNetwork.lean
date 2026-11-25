import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic

/-!
# Scalar contraction and decorations of a network

Each oriented edge has a tail port and a head port. Loops still have two
ports, and distinct edges may have the same endpoints. The local coordinate
at a vertex is one index for each incident port. The transformation below
implements the sum over vertex decorations by adding the two endpoint
decorations to the index of every wire.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical
noncomputable section

section

/-- A network with distinguishable wires and two ports per wire. -/
structure PortGraph (V E : Type*) where
  tail : E → V
  head : E → V

namespace PortGraph

variable {V E : Type*} (G : PortGraph V E)

/-- Incoming and outgoing ports are distinguished even for a loop. -/
def vertex (e : E) : Bool → V
  | false => G.tail e
  | true => G.head e

/-- The ports belonging to one vertex. -/
abbrev Port (v : V) := {p : E × Bool // G.vertex p.1 p.2 = v}

/-- Read the entries on all ports of a vertex from a global wire assignment. -/
def atVertex {A : E → Type*} (a : (e : E) → A e) (v : V) (p : G.Port v) : A p.1.1 := a p.1.1

variable {K : Type*} [CommSemiring K] [Fintype V] [Fintype E]

/-- Multiply local entries and sum over all shared wire indices. -/
def contraction {A : E → Type*} [∀ e, Fintype (A e)]
    (U : (v : V) → ((p : G.Port v) → A p.1.1) → K) : K :=
  ∑ a, ∏ v, U v (G.atVertex a v)

variable (D : Type*) [Fintype D]

/-- The index of a decorated wire contains the old tensor index and the
decorations of its two ends, in tail-to-head order. -/
abbrev DecoratedIndex (A : E → Type*) (e : E) := A e × D × D

private def ownDecoration (p : Bool) (pair : D × D) : D := if p then pair.2 else pair.1

/-- A transformed table accepts one decoration consistent with the record
on every port. The tail of each edge checks its two endpoint decorations.
The original table may already include any vertex tests. -/
def decoratedTable {A : E → Type*}
    (U : (v : V) → D → ((p : G.Port v) → A p.1.1) → K)
    (valid : E → D → D → Prop) (v : V)
    (a : (p : G.Port v) → DecoratedIndex D A p.1.1) : K :=
  ∑ d : D, if (∀ p : G.Port v, ownDecoration D p.1.2 (a p).2 = d) ∧
      (∀ p : G.Port v, p.1.2 = false → valid p.1.1 (a p).2.1 (a p).2.2)
    then U v d (fun p => (a p).1) else 0

private theorem decorated_product {A : E → Type*}
    (U : (v : V) → D → ((p : G.Port v) → A p.1.1) → K)
    (valid : E → D → D → Prop) (a : (e : E) → DecoratedIndex D A e) :
    (∏ v, G.decoratedTable D U valid v (G.atVertex a v)) =
      ∑ d : V → D, if (∀ e, (a e).2 = (d (G.tail e), d (G.head e))) ∧
        (∀ e, valid e (d (G.tail e)) (d (G.head e))) then
          ∏ v, U v (d v) (G.atVertex (fun e => (a e).1) v) else 0 := by
  rw [show (∏ v, G.decoratedTable D U valid v (G.atVertex a v)) = _ from Fintype.prod_sum _]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Fintype.prod_ite_zero]
  congr 1
  apply propext
  constructor
  · intro h
    have header (e : E) : (a e).2 = (d (G.tail e), d (G.head e)) :=
      Prod.ext ((h (G.tail e)).1 ⟨(e,false), rfl⟩) ((h (G.head e)).1 ⟨(e,true), rfl⟩)
    refine ⟨header, fun e => ?_⟩
    have hh := (h (G.tail e)).2 ⟨(e,false), rfl⟩ rfl
    change valid e (a e).2.1 (a e).2.2 at hh
    simpa only [header] using hh
  · rintro ⟨hh, hv⟩ v
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨e, b⟩, rfl⟩
      cases b <;> simp [atVertex, ownDecoration, hh, vertex]
    · rintro ⟨⟨e,b⟩, _⟩ (rfl : b = false)
      simpa [atVertex, hh] using hv e

/-- Packing both endpoint decorations onto every wire implements exactly the
sum over legal decorations, over every commutative semiring. An isolated
vertex contributes its sum over permitted local decorations. -/
theorem contraction_decoratedTable {A : E → Type*} [∀ e, Fintype (A e)]
    (U : (v : V) → D → ((p : G.Port v) → A p.1.1) → K)
    (valid : E → D → D → Prop) :
    G.contraction (G.decoratedTable D U valid) =
      ∑ d : V → D, if ∀ e, valid e (d (G.tail e)) (d (G.head e)) then
        G.contraction (fun v => U v (d v)) else 0 := by
  unfold contraction
  simp_rw [G.decorated_product D U valid]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hv : ∀ e, valid e (d (G.tail e)) (d (G.head e))
  · simp only [hv, implies_true, and_true, ite_true]
    let enc (a : (e : E) → A e) (e : E) : DecoratedIndex D A e :=
      (a e, d (G.tail e), d (G.head e))
    symm
    apply Fintype.sum_of_injective enc
    · exact Function.LeftInverse.injective (g := fun z e => (z e).1) (fun _ => rfl)
    · intro a ha
      apply ite_eq_right
      intro h
      apply ha
      refine ⟨fun e => (a e).1, funext fun e => ?_⟩
      exact Prod.ext rfl (h e).symm
    · intro a
      simp [enc]
  · simp [hv]

end PortGraph
end

end

end SpectralBooks
end LinearAlgebra
end OAI
