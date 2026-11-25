import OAI.Hierarchy.TaggedWireRoutes
import OAI.LinearAlgebra.SpectralBooks.ChordGraph.BoundedPatchReplacementWiring

namespace OAI
/-! # The ordered native endpoints of each physical edge row -/
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
variable {n S : ℕ}

def rowGraph (ends : Fin n→Chord S) : PortGraph (Fin S) (Fin n) :=
  ⟨fun e=>(ends e).1.1,fun e=>(ends e).1.2⟩

def orderedChord (a b : Fin S) (different : a≠b) : Chord S :=
  if h : a<b then ⟨(a,b),h⟩ else ⟨(b,a),lt_of_le_of_ne (le_of_not_gt h) different.symm⟩

open scoped Classical in
noncomputable def filledChord {K r : ℕ} (A : PortGraph (Fin K) (Fin r)) (pad : Chord K) (i : Fin r) :=
  if h:A.tail i=A.head i then pad else orderedChord (A.tail i) (A.head i) h

end Hierarchy.WireTelescope

end OAI
