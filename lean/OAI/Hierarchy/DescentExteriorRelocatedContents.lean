import OAI.Hierarchy.DescentExteriorContent

namespace OAI
/-! # Transporting the contents of all seventeen banks through the native copy -/
namespace Hierarchy.DescentExteriorShelf
open DescentExterior DescentGL Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

theorem relocated_loaded {j r t e w : ℕ} (base out : ℕ) (M : Fin e→Layout (j+(j+r)))
    (x : Fin e→Plane j r→Fin t→Bool) (z : Hidden e j r t→Bool) (m : Memory w)
    (apart : base+32*span j r t e≤out) (room : out+17*span j r t e<2^w)
    (old : Loaded base M x z m) : Loaded out M x z (relocated j r t e base out m) := by
  have copied := (relocate_run (j:=j) (r:=r) (t:=t) (e:=e) base out m apart room).2.2.1
  intro i u hu
  exact (copied i u hu).trans (old i u hu)

end
end Hierarchy.DescentExteriorShelf

end OAI
