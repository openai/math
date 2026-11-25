import OAI.Computability.BorderVNP.CellPacketGeometryPublishedCell
import OAI.Computability.BorderVNP.CellTeamGeometryCharge

/-! # Typed cell placements at the two marker ranges of the actual terminal emitter -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native

open CellSparse CellSparse.Packet CellSparse.Packet.Source SiteWords VPVNP.BurstRAM RoutingISA CellPacket

variable {a C p d dest H : ℕ} {O E : Type} (G : SiteWords.Directory (Fin a) O C) (ptr : O → E)
variable (hf : C+G.words.length+C≤2^p) (hs : C+(Schema.coords (G.referenceRows ptr).length).length+C≤2^d)
variable (mem : ℕ → ℕ) (slot : O → ℕ) (fs : O → List Factor)
variable (ext scratch burst : Fin C → ℕ) (external : Fin C → List Bool)

/-- The placement constructed from the true public and descriptor ranges of
the same terminal output. External and scratch arenas come from the native task table. -/
def atRanges (c : Fin C) : Placed O :=
  let pub := sectionRange mem dest (Markers.start hf c) (Markers.stop hf c)
  let tab := sectionRange mem (descriptorBank dest p) (Markers.start hs c) (Markers.stop hs c)
  G.placed c H slot fs pub.1 tab.1 (ext c) (scratch c) (burst c) (external c)

theorem atRanges_shape : TypedBatch.SourceShape
    (atRanges (dest := dest) (H := H) G ptr hf hs mem slot fs ext scratch burst external) G :=
  ⟨fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

/-- The same concrete placements provide the complete prepass metadata inputs
and source-shape fields used by dispatch and the signed cell observation. -/
theorem Published.places {arg : E → ℕ} (published : Published G p d dest H ptr arg mem)
    (address : ∀ j, arg (ptr j)=slot j) :
    ∃ hf : C+G.words.length+C≤2^p, ∃ hs : C+(Schema.coords (G.referenceRows ptr).length).length+C≤2^d,
      let places := atRanges (dest := dest) (H := H) G ptr hf hs mem slot fs ext scratch burst external
      TypedBatch.SourceShape places G ∧
      ∀ c, CellMemory (places c) ((places c).publicBase+((Supplement.prefixParts (places c)).flatMap Part.publicBuffer).length)
        (descriptorBank dest p+mem (descriptorBank dest p+(2^d+(Markers.stop hs c).val))) mem := by
  obtain ⟨f,s,cell⟩ := published.cells slot fs address
  exact ⟨f,s,atRanges_shape G ptr f s mem slot fs ext scratch burst external,
    fun c => cell c (ext c) (scratch c) (burst c) (external c)⟩

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
