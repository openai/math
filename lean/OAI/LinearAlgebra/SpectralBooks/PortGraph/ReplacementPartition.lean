import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementAssembly

/-! # Recovering an original graph by gluing its induced patches -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PortGraph

noncomputable section
open scoped Classical

universe u
variable {V E J : Type u} (G : PortGraph V E) (p : V → J) [Fintype V] [Fintype E]

/-- A cut edge supplies one named stub in each of its endpoint occurrences. -/
def boundaryPairing : StubPairing (G.PatchBoundary p) where
  Wire := G.CrossEdge p
  ends :=
    { toFun := fun q => if q.2 then ⟨p (G.head q.1.1),⟨q.1,Or.inr rfl⟩⟩
        else ⟨p (G.tail q.1.1),⟨q.1,Or.inl rfl⟩⟩
      invFun := fun s => (s.2.1, if p (G.tail s.2.1.1) = s.1 then false else true)
      left_inv := by
        rintro ⟨e,(_|_)⟩ <;> simp [e.property]
      right_inv := by
        rintro ⟨j,⟨e,h⟩⟩
        rcases h with rfl | rfl <;> simp [e.property] }
  cross e := e.property

/-- The induced old patch, keeping both internal edges and all outside stubs. -/
def originalPiece (j : J) : OpenPiece (G.PatchBoundary p j) where
  Vertex := {v : V // p v = j}
  Edge := G.PatchInternal p j
  graph :=
    { tail := fun e => ⟨G.tail e.1,e.property.1⟩
      head := fun e => ⟨G.head e.1,e.property.2⟩ }
  attach s := if h : p (G.tail s.1.1) = j then ⟨G.tail s.1.1,h⟩
    else ⟨G.head s.1.1,s.property.resolve_left h⟩

def originalVertexEquiv : StubPairing.Vertex (G.originalPiece p) ≃ V :=
  Equiv.sigmaFiberEquiv p

/-- Recover the original edge name by forgetting whether this was an internal
edge or an exterior wire. -/
def originalEdgeEquiv : (G.boundaryPairing p).Edge (G.originalPiece p) ≃ E where
  toFun
    | .inl e => e.1
    | .inr ⟨_,e⟩ => e.1
  invFun e := if h : p (G.tail e) = p (G.head e) then .inr ⟨_,⟨e,rfl,h.symm⟩⟩
    else .inl ⟨e,h⟩
  left_inv := by
    rintro (⟨e,h⟩ | ⟨j,⟨e,ht,hh⟩⟩)
    · simp [h]
    · subst j
      simp [hh.symm]
  right_inv e := by by_cases h : p (G.tail e) = p (G.head e) <;> simp [h]

theorem original_incidence (e : (G.boundaryPairing p).Edge (G.originalPiece p)) (b : Bool) :
    G.originalVertexEquiv p (((G.boundaryPairing p).assemble (G.originalPiece p)).vertex e b) =
      G.vertex (G.originalEdgeEquiv p e) b := by
  rcases e with e | ⟨j,e⟩
  · cases b with
    | false =>
      change ((G.originalPiece p (p (G.tail e.1))).attach ⟨e,Or.inl rfl⟩).1 = G.tail e.1
      simp [originalPiece]
    | true =>
      change ((G.originalPiece p (p (G.head e.1))).attach ⟨e,Or.inr rfl⟩).1 = G.head e.1
      simp [originalPiece, e.property]
  · cases b <;> rfl

end
end PortGraph

end SpectralBooks
end LinearAlgebra
end OAI
