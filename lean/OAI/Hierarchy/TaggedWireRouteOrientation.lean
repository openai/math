import OAI.Hierarchy.TaggedWireWalkOrientation
import OAI.Hierarchy.TaggedWireChordRouter

namespace OAI
/-! # Reindexing true directed endpoint rows onto their sorted physical chords -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe
open scoped Classical BigOperators

variable {S : ℕ} {E D : Type}

theorem oriented_width (G : PortGraph (Fin S) E) (e : E) (different : G.tail e≠G.head e) (w : ℕ) :
    G.chordWidth e w=w • unitChord (orderedChord (G.tail e) (G.head e) different) := by
  by_cases h:G.tail e<G.head e
  · simp [PortGraph.chordWidth,orderedChord,h,unitChord,Finsupp.smul_single]
  · have swap := lt_of_le_of_ne (le_of_not_gt h) different.symm
    simp [PortGraph.chordWidth,orderedChord,h,swap,unitChord,Finsupp.smul_single]

end Hierarchy.WireTelescope

end
end OAI
