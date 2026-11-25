import OAI.LinearAlgebra.SpectralBooks.ChordGraph.BoundedPatchReplacementWiring
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortWiringClass

/-! # The coordinate representative of a width-weighted chord graph -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace ChordGraph

open SiteTensor
open scoped BigOperators Classical

/-- The coordinate test on the individual ports represents the chord graph
class used by spectral straightening. Width-zero chords have a unique label. -/
theorem ofRaw_raw {k : ℕ} [Nonempty (Fin k)] (F : Type*) [Field F] (g : Widths k) :
    ofRaw (raw F g) = graphClass F g := by
  have he : ofRaw (raw F g) = ofRaw ((portGraph k).rawWiring F (Index g)) :=
    ofRaw_eq_iff.mpr (Raw.reindex_equivalent (X := raw F g) (Y := (portGraph k).rawWiring F (Index g))
      (fun _ => Equiv.refl _) fun _ => rfl)
  rw [he]
  rw [PortGraph.ofRaw_rawWiring]
  change (∏ e : Chord k, ofRaw ((Raw.diagonal (Fin 2) F (Fin (2 ^ g e))).group
    ![e.val.1, e.val.2])) = _
  simp_rw [ofRaw_group_diagonal_fin_pow]
  symm
  exact Finsupp.prod_fintype _ _ (fun _ => pow_zero _)

end ChordGraph

end SpectralBooks
end LinearAlgebra
end OAI
