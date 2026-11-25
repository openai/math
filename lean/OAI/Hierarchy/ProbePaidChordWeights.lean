import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortChordWidths

namespace OAI
/-! # Positive paid widths determine their parallel-edge tensor counts -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical
theorem positive_chords {K : ℕ} {E : Type} [Fintype E]
    (G H : PortGraph (Fin K) E) (weights : E→ℕ)
    (same : ∀e,0<weights e→G.tail e=H.tail e ∧ G.head e=H.head e) :
    G.chordWidths weights=H.chordWidths weights := by
  apply Finset.sum_congr rfl
  intro e _
  by_cases positive : 0<weights e
  · obtain ⟨tailEq,headEq⟩:=same e positive
    simp only [PortGraph.chordWidth,tailEq,headEq]
  · have empty : weights e=0:=by omega
    unfold PortGraph.chordWidth
    simp [empty]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
