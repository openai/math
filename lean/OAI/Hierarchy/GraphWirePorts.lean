import OAI.Hierarchy.GraphContractions
import OAI.LinearAlgebra.SpectralBooks.PortNetwork

namespace OAI
/-! # Splitting the vertex coefficients of a contraction into wire ends

Every incidence of a vertex in a loopless graph specifies exactly one of the
two physical ends of the edge. A collection of physical labels contributes a
monomial precisely when the labels at the two ends of each edge coincide.
-/

namespace Hierarchy.IncidenceGraph

open LinearAlgebra.SpectralBooks
open scoped BigOperators Classical
noncomputable section

variable (G : IncidenceGraph)

/-- Orient the physical ends of an edge from its left endpoint to its right endpoint. -/
def toPortGraph : PortGraph G.V G.E := ⟨G.left, G.right⟩

def portOwner (p : G.E × Bool) : G.V := G.toPortGraph.vertex p.1 p.2

@[simp] theorem portOwner_false (e : G.E) : G.portOwner (e, false) = G.left e := rfl
@[simp] theorem portOwner_true (e : G.E) : G.portOwner (e, true) = G.right e := rfl

/-- At a fixed vertex, retaining the end bit gives a bijection between incident
edges and physical legs owned by the vertex. -/
def incidentPortEquiv (v : G.V) : G.Incident v ≃ {p : G.E × Bool // G.portOwner p = v} where
  toFun e := if h : G.left e.val = v then ⟨(e.val, false), h⟩
    else ⟨(e.val, true), e.property.resolve_left h⟩
  invFun p := ⟨p.val.1, by
    obtain ⟨⟨e,b⟩, he⟩ := p
    cases b with
    | false => exact Or.inl he
    | true => exact Or.inr he⟩
  left_inv e := by
    apply Subtype.ext
    by_cases h : G.left e.val = v <;> simp [h]
  right_inv p := by
    obtain ⟨⟨e,b⟩, he⟩ := p
    cases b with
    | false =>
      change G.left e = v at he
      simp [he]
    | true =>
      change G.right e = v at he
      have hn : G.left e ≠ v := fun hl => G.loopless e (hl.trans he.symm)
      simp [hn]

/-- Recover the arguments of a vertex table from its owned physical legs. -/
def portAssemble {q : ℕ} (v : G.V) (x : {p : G.E × Bool // G.portOwner p = v} → Fin q)
    (e : G.Incident v) : Fin q := x (G.incidentPortEquiv v e)

def portAssignment {q : ℕ} (x : G.E × Bool → Fin q) (v : G.V) : G.Incident v → Fin q :=
  G.portAssemble v (fun p => x p.val)

@[simp] theorem portAssignment_left {q : ℕ} (x : G.E × Bool → Fin q) (e : G.E) :
    G.portAssignment x (G.left e) ⟨e, Or.inl rfl⟩ = x (e, false) := by
  simp [portAssignment, portAssemble, incidentPortEquiv]

@[simp] theorem portAssignment_right {q : ℕ} (x : G.E × Bool → Fin q) (e : G.E) :
    G.portAssignment x (G.right e) ⟨e, Or.inr rfl⟩ = x (e, true) := by
  simp [portAssignment, portAssemble, incidentPortEquiv, G.loopless e]

/-- The local table choices come from a global edge labeling exactly when the
physical equality test succeeds for every edge. -/
theorem exists_labeling_iff_port_eq {q : ℕ} (x : G.E × Bool → Fin q) :
    (∃ b : G.E → Fin q, ∀ v (e : G.Incident v), b e.val = G.portAssignment x v e) ↔
      ∀ e : G.E, x (e, false) = x (e, true) := by
  constructor
  · rintro ⟨b, hb⟩ e
    have hl := hb (G.left e) ⟨e, Or.inl rfl⟩
    have hr := hb (G.right e) ⟨e, Or.inr rfl⟩
    simpa only [portAssignment_left, portAssignment_right] using hl.symm.trans hr
  · intro h
    refine ⟨fun e => x (e, false), fun v ⟨e, he⟩ => ?_⟩
    rcases he with hl | hr
    · subst v
      exact (G.portAssignment_left x e).symm
    · subst v
      exact (h e).trans (G.portAssignment_right x e).symm

end
end Hierarchy.IncidenceGraph

end OAI
