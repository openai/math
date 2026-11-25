import OAI.ThreeFlat.Diagonal.CompressorWordEncoding
import OAI.ThreeFlat.Diagonal.PhysicalRecordFamily
import OAI.ThreeFlat.Diagonal.PhysicalRunRootNumber

namespace OAI
/-! # Terminal wire widths and physical factor numbers of the selected history -/

noncomputable section
namespace Hierarchy.GridPhysicalSelector
open ThreeFlat.Diagonal.PhysicalStage
variable {F : Type} [Field F] {d l : ℕ} {S : State d l}

abbrev bits (r : Run F S) (h : r.plan.History) := (r.terminalLayer h).state.widthSum

/-- The terminal factor index is the physical base ordinal times the number
of lanes plus the residual lane ordinal. It is also the order of the archive. -/
abbrev siteOrder (r : Run F S) (h : r.plan.History) := r.terminalOrderEquiv h

end Hierarchy.GridPhysicalSelector
end

namespace Hierarchy.GridPhysicalAdmission
open ThreeFlat.Diagonal
noncomputable section

/-- The resource reader's lane j is the zero-cursor input bucket j. -/
def initialLane {k : ℕ} (positive : 0<k) (j : Fin (2^k)) :
    Fin k × Computability.VPVNP.Compression.BitWord k :=
  (⟨0,positive⟩,(CompressorPacking.Native.tagOrdinal k).symm j)

end
end Hierarchy.GridPhysicalAdmission

end OAI
