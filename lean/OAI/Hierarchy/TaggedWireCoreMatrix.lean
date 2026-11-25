import OAI.Hierarchy.TaggedWireCoreLayout
import OAI.Hierarchy.TaggedWireInstalledRows
import OAI.Hierarchy.TaggedWireSettledMatrix
import OAI.Hierarchy.TaggedWireInitialStock

namespace OAI
/-! # The terminal equality matrices on the core board's real named walks -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe
open scoped Classical BigOperators
variable {K r : ℕ}

theorem filled_width (A : PortGraph (Fin K) (Fin r)) (pad : Chord K) (bits : Fin r→ℕ)
    (empty : ∀i,A.tail i=A.head i→bits i=0) : installedWidths (filledChord A pad) bits=A.chordWidths bits := by
  unfold installedWidths PortGraph.chordWidths
  apply Finset.sum_congr rfl
  intro i _
  by_cases h:A.tail i=A.head i
  · simp [empty i h,PortGraph.chordWidth]
  · simpa only [filledChord,dite_eq_right h] using (oriented_width A i h (bits i)).symm

end Hierarchy.WireTelescope

end
end OAI
