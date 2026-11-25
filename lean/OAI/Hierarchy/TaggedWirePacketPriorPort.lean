import OAI.Hierarchy.TaggedWireNamedAperture

namespace OAI
noncomputable section
namespace Hierarchy.WireTelescope.PacketTurns
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
variable {S n : ℕ} (old : Fin n→Chord S) (bits : Fin n→ℕ)

def priorPort (i : Fin n) (j : Fin (bits i)) (b : Bool) {s : Fin S} (atSite : (rowGraph old).vertex i b=s) :
    (bitGraph (rowGraph old) bits).Port s := ⟨(⟨i,j⟩,b),by cases b <;> exact atSite⟩

end Hierarchy.WireTelescope.PacketTurns

end
end OAI
