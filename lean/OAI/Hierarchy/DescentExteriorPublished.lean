import OAI.Hierarchy.DescentExteriorReelPrograms

import OAI.Hierarchy.DescentExteriorBroadcast

namespace OAI
/-! # The native dated matrix accumulator and the final slab broadcast -/
namespace Hierarchy.DescentExteriorShelf
open DescentGL DescentExterior DescentExteriorMatrixUpdate Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {w e j r t : ℕ}
set_option quotPrecheck false
local notation "H" => span j r t e

theorem published_loaded (origin age : ℕ) (cells : ℕ→Cell) (m : Memory w)
    (P M : Fin e→Layout (j+(j+r))) (x : Fin e→Plane j r→Fin t→Bool) (z : Hidden e j r t→Bool)
    (printed : Loaded origin P x z m) (early : ∀i<age,(cells i).updated < origin)
    (read : ∀s : Fin e,reached cells m age (cells age).old.base=((matrixCode (M s)).val:Word w)) :
    Loaded origin M x z (published j r t e origin age cells m) :=
  issued_loaded origin (cells age).old.base (reached cells m age) M P x z
    (frames origin P x z cells m age printed early) read

end
end Hierarchy.DescentExteriorShelf

end OAI
