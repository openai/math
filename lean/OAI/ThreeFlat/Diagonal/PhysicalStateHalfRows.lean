import OAI.ThreeFlat.Diagonal.PhysicalArchiveRows
import OAI.ThreeFlat.Diagonal.CompressorHalfValues

namespace OAI
/-! # Half-edge rows attached to numbered physical sites -/

namespace ThreeFlat.Diagonal.PhysicalStage
open CompressorPacking.Native.ShrinkStage
variable {d l : ℕ} {X : State d l}
namespace State
structure HalfRows (O : X.ArchiveSites) (safe : ℕ→Prop) (mem : ℕ→ℕ) : Prop where
  count : ∀ z,mem (O.layer.incident+(O.ord z).val*2)=2*d
  edge : ∀ z (i : Fin (2*d)),mem (mem (O.layer.incident+(O.ord z).val*2+1)+4*i.val)=
    Halves.edgeNumber X.order (Halves.sourceHalf X.graph (X.chart.symm z) i)
  width : ∀ z (i : Fin (2*d)),mem (mem (O.layer.incident+(O.ord z).val*2+1)+4*i.val+2)=
    X.width (Halves.sourceHalf X.graph (X.chart.symm z) i)
  start : ∀ z (i : Fin (2*d)),mem (mem (O.layer.incident+(O.ord z).val*2+1)+4*i.val+3)=
    Halves.prefixValue X.graph X.width (X.chart.symm z) i
  headerSafe : ∀ z (k : Fin 2),safe (O.layer.incident+(O.ord z).val*2+k.val)
  entriesSafe : ∀ z (i : Fin (2*d)) (k : Fin 4),safe (mem (O.layer.incident+(O.ord z).val*2+1)+4*i.val+k.val)

theorem HalfRows.transfer {O : X.ArchiveSites} {safe safe' : ℕ→Prop} {mem out : ℕ→ℕ}
    (H : HalfRows O safe mem) (same : ∀ i,safe i → out i=mem i) (mono : ∀ i,safe i→safe' i) :
    HalfRows O safe' out := by
  have pointer z : out (O.layer.incident+(O.ord z).val*2+1)=mem (O.layer.incident+(O.ord z).val*2+1) :=
    same _ (H.headerSafe z 1)
  refine ⟨fun z=>(same _ (H.headerSafe z 0)).trans (H.count z),?_,?_,?_,
    fun z k=>mono _ (H.headerSafe z k),?_⟩
  · intro z i;rw [pointer];exact (same _ (H.entriesSafe z i 0)).trans (H.edge z i)
  · intro z i;rw [pointer];exact (same _ (H.entriesSafe z i 2)).trans (H.width z i)
  · intro z i;rw [pointer];exact (same _ (H.entriesSafe z i 3)).trans (H.start z i)
  · intro z i k;rw [pointer];exact mono _ (H.entriesSafe z i k)
end State
end ThreeFlat.Diagonal.PhysicalStage

end OAI
