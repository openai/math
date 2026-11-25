import OAI.LinearAlgebra.SpectralBooks.ChordGraph.BoundedPatchReplacementWiring
import OAI.Computability.VPVNP.RAMSerialization

namespace OAI
/-! # Bit coordinates at a vertex of a chord graph -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open LinearAlgebra.SpectralBooks ChordGraph
variable {S : ℕ}

abbrev SiteBit (W : Widths S) (s : Fin S) := (p : (portGraph S).Port s) × Fin (W p.1.1)

/-- The real signed site's per-chord bit order, including chords of width zero. -/
def siteBits (W : Widths S) (s : Fin S) : State W s ≃ (SiteBit W s→Bool) :=
  (Equiv.piCongrRight (fun p : (portGraph S).Port s=>Computability.VPVNP.RAMSerialization.wordBits (W p.1.1))).trans
    (Equiv.piCurry (fun (p : (portGraph S).Port s) (_ : Fin (W p.1.1))=>Bool)).symm

end Hierarchy.WireTelescope.CalendarTape
end

end OAI
