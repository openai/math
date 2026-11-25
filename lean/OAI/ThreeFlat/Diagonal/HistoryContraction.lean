import OAI.ThreeFlat.Diagonal.WireRewrite
import OAI.LinearAlgebra.SpectralBooks.PortWiring

namespace OAI
/-! # Iterating term-dependent local wire rewrites

A step changes the port graph, chooses the placement of every old site and
supplies one new kernel per destination. The next rewrite can depend on the
whole prefix of chosen terms. The terminal graph is contracted only after
all these choices have been made.
-/

namespace ThreeFlat.Diagonal.HistoryContraction

open LinearAlgebra.SpectralBooks
open scoped BigOperators Classical

/-- The finite sites, directed wires, and wire alphabets of one graph. -/
structure Shape where
  Site : Type
  Edge : Type
  graph : PortGraph Site Edge
  Label : Edge → Type
  [siteFintype : Fintype Site]
  [edgeFintype : Fintype Edge]
  [labelFintype : ∀ e, Fintype (Label e)]

attribute [instance] Shape.siteFintype Shape.edgeFintype Shape.labelFintype

abbrev Shape.Half (S : Shape) := S.graph.State S.Label
abbrev Shape.Factors (S : Shape) (F : Type*) := ∀ i, S.Half i → F
abbrev Shape.Boundary (S : Shape) := ∀ e, S.Label e

noncomputable def Shape.contract (S : Shape) {F : Type*} [CommSemiring F] (u : S.Factors F) : F :=
  S.graph.contraction u

/-- Each term has its own successor topology. The kernel at `v` has
access to the new incident port values and all the old half-indices at
sites moved to `v`. -/
structure Rewrite (S : Shape) (F : Type*) [CommSemiring F] where
  count : ℕ
  target : Fin count → Shape
  owner : ∀ t, S.Site → (target t).Site
  kernel : ∀ t v, (∀ i : {i // owner t i = v}, S.Half i) → (target t).Half v → F
  wire_eq : ∀ a : ∀ i, S.Half i, S.graph.wiring S.Label a =
    ∑ t, (target t).contract (fun v b => kernel t v (fun i => a i) b)

variable {S : Shape} {F : Type*} [CommSemiring F]

/-- Fold the whole old local operand into its new unique owner. -/
noncomputable def Rewrite.move (R : Rewrite S F) (t : Fin R.count) (u : S.Factors F) :
    (R.target t).Factors F := fun v b =>
  ∑ a : ∀ i : {i // R.owner t i = v}, S.Half i,
    R.kernel t v a b * ∏ i : {i // R.owner t i = v}, u i (a i)

theorem Rewrite.contract_eq (R : Rewrite S F) (u : S.Factors F) :
    S.contract u = ∑ t, (R.target t).contract (R.move t u) := by
  classical
  rw [Shape.contract, PortGraph.contraction_eq_wiring]
  exact contraction_wire_rewrite R.owner (S.graph.wiring S.Label)
    (fun t v (z : (R.target t).Boundary) a => R.kernel t v a ((R.target t).graph.atVertex z v))
    R.wire_eq u

/-- Steps and the terminal stage of an adaptive compression schedule. -/
inductive Plan (F : Type*) [CommSemiring F] : Shape → Type _ where
  | done (S : Shape) : Plan F S
  | step {S : Shape} (R : Rewrite S F) (next : ∀ t, Plan F (R.target t)) : Plan F S

namespace Plan

/-- One canonical term index at every visited step. -/
def History : {S : Shape} → Plan F S → Type
  | _, .done _ => Unit
  | _, .step R next => (t : Fin R.count) × (next t).History

noncomputable instance historyFintype : {S : Shape} → (P : Plan F S) → Fintype P.History
  | _, .done _ => inferInstanceAs (Fintype Unit)
  | _, .step R next =>
    letI : ∀ t, Fintype (next t).History := fun t => historyFintype (next t)
    inferInstanceAs (Fintype ((t : Fin R.count) × (next t).History))

/-- The graph remaining after exactly the term history `h`. -/
def finish : {S : Shape} → (P : Plan F S) → P.History → Shape
  | _, .done S, _ => S
  | _, .step _ next, h => (next h.1).finish h.2

/-- Composition of the actual placement maps along a history. -/
def destination : {S : Shape} → (P : Plan F S) → (h : P.History) → S.Site → (P.finish h).Site
  | _, .done _, _ => id
  | _, .step R next, h => (next h.1).destination h.2 ∘ R.owner h.1

/-- Compute the terminal site's map by contracting its ancestors from the
leaves up. It can then be sampled on any choice of final wire labels. -/
noncomputable def cells : {S : Shape} → (P : Plan F S) → (h : P.History) →
    S.Factors F → (P.finish h).Factors F
  | _, .done _, _ => id
  | _, .step R next, h => fun u => (next h.1).cells h.2 (R.move h.1 u)

/-- Every internal choice and intermediate edge is summed exactly once;
only the final wire assignment remains outside the product of cells. -/
theorem contract_eq_cells (P : Plan F S) (u : S.Factors F) :
    S.contract u = ∑ h : P.History, ∑ b : (P.finish h).Boundary,
      ∏ v, P.cells h u v ((P.finish h).graph.atVertex b v) := by
  induction P with
  | done S =>
    change S.contract u = ∑ _ : Unit, S.contract u
    rw [Fintype.sum_unique]
  | step R next ih =>
    rw [R.contract_eq]
    change (∑ t, (R.target t).contract (R.move t u)) =
      ∑ h : (t : Fin R.count) × (next t).History, _
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro t _
    exact ih t (R.move t u)

/-- A terminal cell depends only on initial local maps at its own ancestor
sites. This accounts for every original local operand, including all its
external inputs. -/
theorem cells_local (P : Plan F S) (h : P.History) (v : (P.finish h).Site)
    (u u' : S.Factors F) (agree : ∀ i, P.destination h i = v → u i = u' i) :
    P.cells h u v = P.cells h u' v := by
  induction P with
  | done S => exact agree v rfl
  | step R next ih =>
    obtain ⟨t,h⟩ := h
    apply ih t
    intro g hg
    funext b
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    have dest : (Plan.step R next).destination ⟨t,h⟩ i.1 = v := by
      change (next t).destination h (R.owner t i.1) = v
      rw [i.2, hg]
    rw [agree i.1 dest]

end Plan
end ThreeFlat.Diagonal.HistoryContraction

end OAI
