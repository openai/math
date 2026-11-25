import OAI.Hierarchy.DescentResetStemKeyReindex

namespace OAI
/-! # Padded lookup into the physically issued predecessor directory -/
namespace Hierarchy.DescentResetStemKeyReindex
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
variable {count pad P oldP w : ℕ}
def paddedParent (src : Fin count→Fin oldP) (oldRoom : oldP≤P) (present : 0<pad→0<P)
    (j : Fin pad) : Fin P :=
  if live : j.val<count then (src ⟨j.val,live⟩).castLE oldRoom else ⟨0,present j.pos⟩

theorem padded_directory (base : ℕ) (src : Fin count→Fin oldP) (oldRoom : oldP≤P)
    (present : 0<pad→0<P) (m : Memory w) (active : Directory base src m)
    (empty : ∀j : Fin pad,count≤j.val→m (base+j.val)=0) :
    Directory base (paddedParent src oldRoom present) m := by
  intro j
  by_cases live : j.val<count
  · simpa only [paddedParent,dite_eq_left live,Fin.val_castLE] using active ⟨j.val,live⟩
  · simpa only [paddedParent,dite_eq_right live,Nat.cast_zero] using empty j (Nat.le_of_not_gt live)

end Hierarchy.DescentResetStemKeyReindex

end OAI
