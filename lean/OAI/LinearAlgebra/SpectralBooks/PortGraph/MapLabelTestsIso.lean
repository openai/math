import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsViews
import OAI.LinearAlgebra.SpectralBooks.UniformDecorations.UniformDecorations

/-! # Invariance of local label tests under map isomorphisms -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace PortGraph.MapLabelTests

variable {A V E W D : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  [Fintype W] [Fintype D] [DecidableEq W]
  {M : RootedMap V E} {H : RootedMap W D}

/-- Transporting the vertex labels through a rooted map isomorphism preserves
the vertex tests and both ordered ports of every edge test. -/
theorem pass_iso (T : MapLabelTests A) (f : M.Iso H) (z : V → A) (z' : W → A)
    (same : ∀ v, z v = z' (f.vertex v)) : T.Pass M z ↔ T.Pass H z' := by
  have slot (e : E) (b : Bool) :
      M.slots _ ⟨(e,b),rfl⟩ = H.slots _ ⟨(f.edge e,b),rfl⟩ :=
    Fin.ext (f.number e b)
  have tail (e : E) : f.vertex (M.graph.tail e) = H.graph.tail (f.edge e) :=
    f.incidence e false
  have head (e : E) : f.vertex (M.graph.head e) = H.graph.head (f.edge e) :=
    f.incidence e true
  unfold Pass
  rw [← f.vertex.forall_congr_right, ← f.edge.forall_congr_right]
  simp only [UniformDecorations.typeAt_iso f, same, slot, tail, head]

end PortGraph.MapLabelTests

end SpectralBooks
end LinearAlgebra
end OAI
