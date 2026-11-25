import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementAssembly
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementDecoder
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RootedMapRelabel

/-! # The reconstructed assembly of a passing decorated map

The decoded occurrences, paired stubs, and chosen trees determine an actual
closed graph. Its vertices, edges and their numbered ends agree with the
decorated input. The same pairing can now be used to expand the occurrences
to their recorded old patches.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PortGraph.ReplacementTemplate

open scoped Classical

variable {V E J I : Type} {T : J → ReplacementTemplate.{0,0,0}} {H : PortGraph V E}
    {num : H.FourPortNumbering} {slot : Numbering T} {z : V → Σ j, (T j).Role}
    {patchId : J → I} {oldEdge : (Σ j, (T j).Stub) → (Σ j, (T j).Stub) → Prop}
    (hv : ∀ v, VertexTest T num slot z v)
    (he : ∀ e, PairTest patchId oldEdge (readEnd hv e false) (readEnd hv e true))

/-- Occurrences carrying equal record identifiers cannot be joined by a cut
wire. Hence the decoded ends form a pairing between distinct occurrences. -/
def decodedPairing [Fintype E] : StubPairing (fun c : Copies (T := T) z ↦ (T c.1).Stub) where
  Wire := OutsideEdge hv
  ends := endsEquiv hv he
  cross e h := (stub_tests hv he e).1 (congrArg (fun c ↦ patchId c.1) h)

variable [∀ j, Fintype (T j).Role] [∀ j, Fintype (T j).Wire]

/-- The prescribed component of an individual replacement occurrence. -/
def treePiece (c : Copies (T := T) z) : OpenPiece (T c.1).Stub where
  Vertex := (T c.1).Role
  Edge := (T c.1).Wire
  graph := (T c.1).graph
  attach := (T c.1).attach

variable [Fintype E]

/-- Reassemble all of the actual edges of the accepted smaller map: cut wires
are kept, and each internal edge is addressed by its occurrence and role. -/
def decodedEdge : E ≃ (decodedPairing hv he).Edge (treePiece (T := T) (z := z)) :=
  (edgePartition hv).symm.trans ((Equiv.refl _).sumCongr (wireEquiv hv he))

theorem decoded_incidence (e : E) (b : Bool) :
    vertexEquiv hv he (H.vertex e b) =
      ((decodedPairing hv he).assemble treePiece).vertex (decodedEdge hv he e) b := by
  obtain ⟨(q | q),rfl⟩ := (edgePartition hv).surjective e
  · have h : decodedEdge hv he (edgePartition hv (.inl q)) = Sum.inl q := by
      exact congrArg ((Equiv.refl _).sumCongr (wireEquiv hv he))
        ((edgePartition hv).symm_apply_apply (.inl q))
    rw [h]
    exact (stub_incidence hv he q b).trans
      ((decodedPairing hv he).vertex_exterior treePiece q b).symm
  · have h : decodedEdge hv he (edgePartition hv (.inr q)) = Sum.inr (wireEquiv hv he q) := by
      exact congrArg ((Equiv.refl _).sumCongr (wireEquiv hv he))
        ((edgePartition hv).symm_apply_apply (.inr q))
    rw [h]
    obtain h := wire_incidence hv he q b
    generalize hq : wireEquiv hv he q = x at *
    obtain ⟨c,d⟩ := x
    exact h.trans ((decodedPairing hv he).vertex_internal treePiece c d b).symm

/-- Expand each accepted local tree to its recorded old piece, reusing the
same external incidence at the original named stubs. No test for an old edge
depends on which internal tree role read the stub. -/
def expandedOld (old : ∀ j, OpenPiece (T j).Stub) :=
  (decodedPairing hv he).assemble (fun c ↦ old c.1)

omit [∀ j, Fintype (T j).Role] [∀ j, Fintype (T j).Wire] in
theorem all_external_old_tests (e : (decodedPairing hv he).Wire) :
    oldEdge ⟨((decodedPairing hv he).ends (e,false)).1.1,((decodedPairing hv he).ends (e,false)).2⟩
      ⟨((decodedPairing hv he).ends (e,true)).1.1,((decodedPairing hv he).ends (e,true)).2⟩ :=
  (stub_tests hv he e).2

end PortGraph.ReplacementTemplate

end

end SpectralBooks
end LinearAlgebra
end OAI
