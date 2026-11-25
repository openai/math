import OAI.Hierarchy.TaggedWireRowGraph

namespace OAI
/-! # Original commodity and permanent-edge rows of an installed graph -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open scoped Classical

namespace ChosenPackets
variable {S g p : ℕ}
variable (G : PortGraph (Fin S) (Fin g)) (P : PortGraph (Fin S) (Fin p)) (pad : Chord S)

/-- Original virtual stock IDs and original permanent row IDs occupy disjoint
slots, even when both endpoints of two slots coincide. -/
def unionRows : Fin (g+p)→Chord S :=
  Sum.elim (filledChord G pad) (filledChord P pad) ∘ finSumFinEquiv.symm

def stockRow (i : Fin g) : Fin (g+p) := finSumFinEquiv (.inl i)
def paidRow (e : Fin p) : Fin (g+p) := finSumFinEquiv (.inr e)

end ChosenPackets
end Hierarchy.WireTelescope
end

end OAI
