import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomParameters
import OAI.Computability.BorderVNP.CellPacketGeometryExecute
import OAI.Computability.BorderVNP.CellPacketGeometrySchema

/-! # The five selected geometry addresses as actual output columns -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open CellPacketGeometry

/-- Read addresses in the joint private-packet geometry and the marked
bundle sort. The former starts after both banks of the public-word sort.
The latter starts after the 37 scalar controls and their preceding
additional output columns. -/
def GeometryDirectories.published (wordBase publicBits descriptorBits cells chunks
    control preceding bundleBits : ℕ) : GeometryDirectories where
  sorted := descriptorBank wordBase publicBits
  padded := 2^descriptorBits
  stops := cells+3*chunks
  bundlePayload := control+37+preceding
  bundleInverse := control+37+preceding+2^bundleBits

/-- The actual first and exclusive-stop ordinals used by the primary
task builder are the two markers of this same descriptor-sort section. -/
theorem GeometryDirectories.published_markers {cells chunks d : ℕ}
    (wordBase publicBits control preceding bundleBits : ℕ) (c : Fin cells)
    (fit : cells+(Schema.coords chunks).length+cells≤2^d) :
    let g := GeometryDirectories.published wordBase publicBits d cells chunks control preceding bundleBits
    g.sorted+g.padded+c.val=descriptorBank wordBase publicBits+2^d+(Markers.start fit c).val ∧
    g.sorted+g.padded+(g.stops+c.val)=descriptorBank wordBase publicBits+2^d+(Markers.stop fit c).val ∧
      g.stops+cells≤g.padded := by
  rw [Schema.coords_length] at fit
  simp only [published,Markers.start,Markers.stop,Schema.coords_length,fit,and_self]

/-- Both read bases of the native six-word retained-bundle directory are
the physically emitted payload and inverse banks. -/
theorem GeometryDirectories.published_bundle (wordBase publicBits descriptorBits cells chunks
    control preceding bundleBits : ℕ) :
    let g := GeometryDirectories.published wordBase publicBits descriptorBits cells chunks control preceding bundleBits
    g.bundlePayload=control+37+preceding ∧ g.bundleInverse=g.bundlePayload+2^bundleBits := ⟨rfl,rfl⟩

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
