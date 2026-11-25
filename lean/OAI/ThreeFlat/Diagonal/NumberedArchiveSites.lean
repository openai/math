import OAI.ThreeFlat.Diagonal.PhysicalArchiveRows
import OAI.ThreeFlat.Diagonal.CompressorWordEncoding

namespace OAI
/-! # Native ordinal of a site in the chronological archive -/
namespace ThreeFlat.Diagonal.PhysicalStage

/-- The physical base ordinal is the high part of the native address and the
binary lane is the low part, in every stored layer. -/
def State.ArchiveSites.Numbered {d l : ℕ} {A : State d l} (O : A.ArchiveSites) : Prop :=
  ∀ x,(O.ord x).val=(A.order (A.chart.symm x).1).val*2^l+
    (CompressorPacking.Native.tagOrdinal l (A.chart.symm x).2).val

end ThreeFlat.Diagonal.PhysicalStage

end OAI
